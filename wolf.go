package main

import (
	"crypto/sha256"
	"encoding/binary"
	"flag"
	"fmt"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"os/signal"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/songgao/water"
	"golang.org/x/crypto/chacha20"
)

const (
	MagicSignature uint32 = 0xACE1FACE
	// TUN_MTU 1000 + 6-bit expansion + UDP/IP headers fits perfectly under 1500
	TUN_MTU              = 1000
	BMP_HEADER_SIZE      = 54
	OP_DATA         byte = 4
	OP_AUTH         byte = 5
	OP_HEARTBEAT    byte = 6
)

var (
	mgr            = &SessionManager{}
	conn           *net.UDPConn
	outboundChan   = make(chan outboundJob, 1000) // Smaller channel to prevent bufferbloat
	origForwarding string
	myAssignedIP   string
	basePass       string
	clientSeq      uint32
	serverSeq      uint32
	sessionCount   int64
	bufferPool     = sync.Pool{
		New: func() interface{} { return make([]byte, 65535) },
	}
)

type UserSession struct {
	Addr       *net.UDPAddr
	HWID       string
	InternalIP string
	SeqIn      uint32
	SeqOut     uint32
	LastSeen   int64
	UserKey    []byte
}

type SessionManager struct {
	ByIP   sync.Map
	ByAddr sync.Map
	ByHWID sync.Map
}

type outboundJob struct {
	payload []byte
	target  *net.UDPAddr
	seq     uint32
	key     []byte
}

// --- High Performance 6-Bit Wolfram-ChaCha ---

func wolframChaCha(data []byte, key []byte, seq uint32) []byte {
	h := sha256.Sum256(binary.BigEndian.AppendUint32(key, seq))
	c, _ := chacha20.NewUnauthenticatedCipher(h[:32], h[20:32])

	seed := int64(binary.BigEndian.Uint64(h[:8]))
	rng := rand.New(rand.NewSource(seed))

	out := make([]byte, len(data))
	for i := range data {
		out[i] = data[i] ^ uint8(rng.Intn(256))
	}
	c.XORKeyStream(out, out)
	return out
}

func encode6Bit(msg []byte, key []byte, seq uint32) []byte {
	payload := append(binary.BigEndian.AppendUint32(nil, MagicSignature), msg...)
	encrypted := wolframChaCha(payload, key, seq)

	vLen := uint32(len(encrypted))
	meta := make([]byte, 8)
	binary.BigEndian.PutUint32(meta[0:4], vLen)
	binary.BigEndian.PutUint32(meta[4:8], seq)

	full := append(meta, encrypted...)

	// Packing: 6 bits per byte.
	bmpBodyLen := (len(full)*8 + 5) / 6
	bmp := bufferPool.Get().([]byte)[:BMP_HEADER_SIZE+bmpBodyLen]

	// BMP Header construction
	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[2:6], uint32(len(bmp)))
	binary.LittleEndian.PutUint32(bmp[10:14], uint32(BMP_HEADER_SIZE))
	binary.LittleEndian.PutUint32(bmp[14:18], 40)
	binary.LittleEndian.PutUint32(bmp[18:22], uint32(bmpBodyLen/3))
	binary.LittleEndian.PutUint32(bmp[22:26], 1)
	binary.LittleEndian.PutUint16(bmp[26:28], 1)
	binary.LittleEndian.PutUint16(bmp[28:30], 24)

	// Bit Packing Logic
	bitCursor := 0
	for _, b := range full {
		for i := 7; i >= 0; i-- {
			bit := (b >> i) & 1
			byteIdx := BMP_HEADER_SIZE + (bitCursor / 6)
			bitPos := 5 - (bitCursor % 6)

			if bitCursor%6 == 0 {
				bmp[byteIdx] = 0x40 // Base intensity to keep pixels "gray-ish"
			}
			bmp[byteIdx] |= (bit << bitPos)
			bitCursor++
		}
	}
	return bmp
}

func decode6Bit(stego []byte, key []byte, seqPtr *uint32) ([]byte, bool) {
	if len(stego) < BMP_HEADER_SIZE+12 {
		return nil, false
	}

	// Bit Unpacking
	totalBits := (len(stego) - BMP_HEADER_SIZE) * 6
	bitStream := make([]byte, (totalBits/8)+1)
	for i := 0; i < totalBits; i++ {
		byteIdx := BMP_HEADER_SIZE + (i / 6)
		bitPos := 5 - (i % 6)
		if byteIdx >= len(stego) {
			break
		}
		bit := (stego[byteIdx] >> bitPos) & 1
		bitStream[i/8] |= (bit << (7 - (i % 8)))
	}

	if len(bitStream) < 8 {
		return nil, false
	}
	vLen := binary.BigEndian.Uint32(bitStream[0:4])
	rSeq := binary.BigEndian.Uint32(bitStream[4:8])

	if vLen == 0 || int(8+vLen) > len(bitStream) {
		return nil, false
	}
	vault := bitStream[8 : 8+vLen]

	curr := atomic.LoadUint32(seqPtr)
	for o := -15; o <= 15; o++ { // Slightly tighter window for speed
		sSeq := uint32(int(rSeq) + o)
		dec := wolframChaCha(vault, key, sSeq)
		if len(dec) > 4 && binary.BigEndian.Uint32(dec[:4]) == MagicSignature {
			if sSeq >= curr {
				atomic.StoreUint32(seqPtr, sSeq+1)
			}
			return dec[4:], true
		}
	}
	return nil, false
}

// --- System Networking & Lifecycle ---

func configureSystem(name, localIP, peerIP string, isServer bool) (string, string) {
	run := func(c string, args ...string) { _ = exec.Command(c, args...).Run() }
	outFwd, _ := exec.Command("sysctl", "-n", "net.ipv4.ip_forward").Output()
	origForwarding = strings.TrimSpace(string(outFwd))

	outRoute, _ := exec.Command("ip", "route", "show", "default").Output()
	fields := strings.Fields(string(outRoute))
	var gw, dev string
	for i, f := range fields {
		if f == "via" {
			gw = fields[i+1]
		}
		if f == "dev" {
			dev = fields[i+1]
		}
	}

	run("ip", "link", "set", "dev", name, "up", "mtu", fmt.Sprintf("%d", TUN_MTU))
	if localIP != "0.0.0.0" {
		run("ip", "addr", "replace", localIP+"/24", "dev", name)
	}

	if isServer {
		run("sysctl", "-w", "net.ipv4.ip_forward=1")
		run("iptables", "-t", "nat", "-F")
		run("iptables", "-t", "nat", "-A", "POSTROUTING", "-o", dev, "-j", "MASQUERADE")
		// MSS Clamping is vital for VPN stability
		run("iptables", "-t", "mangle", "-A", "FORWARD", "-p", "tcp", "--tcp-flags", "SYN,RST", "SYN", "-j", "TCPMSS", "--set-mss", "900")
	} else if localIP != "0.0.0.0" && peerIP != "" {
		run("ip", "route", "add", peerIP, "via", gw, "dev", dev)
		run("ip", "route", "add", "0.0.0.0/1", "dev", name)
		run("ip", "route", "add", "128.0.0.0/1", "dev", name)
	}
	return gw, dev
}

func cleanup(origFwd string) {
	fmt.Println("\n[*] Restoring system networking...")
	_ = exec.Command("sysctl", "-w", "net.ipv4.ip_forward="+origFwd).Run()
	_ = exec.Command("iptables", "-t", "nat", "-F").Run()
	_ = exec.Command("iptables", "-t", "mangle", "-F").Run()
	os.Exit(0)
}

func getHWID() string {
	host, _ := os.Hostname()
	h := sha256.Sum256([]byte(host))
	return fmt.Sprintf("%x", h[:8])
}

func main() {
	lPort := flag.String("l", "9000", "Port")
	tAddrStr := flag.String("t", "", "Target")
	flag.StringVar(&basePass, "p", "Tetralogik@", "Key")
	tunIP := flag.String("ip", "10.0.0.1", "Internal IP")
	isServer := flag.Bool("server", false, "Server Mode")
	flag.Parse()

	cores := runtime.NumCPU()
	runtime.GOMAXPROCS(cores)

	tun, _ := water.New(water.Config{DeviceType: water.TUN})
	pHost := ""
	if *tAddrStr != "" {
		pHost, _, _ = net.SplitHostPort(*tAddrStr)
	}
	configureSystem(tun.Name(), *tunIP, pHost, *isServer)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGINT, syscall.SIGTERM)
	go func() { <-sig; cleanup(origForwarding) }()

	lAddr, _ := net.ResolveUDPAddr("udp", ":"+*lPort)
	conn, _ = net.ListenUDP("udp", lAddr)
	_ = conn.SetReadBuffer(32 * 1024 * 1024)
	_ = conn.SetWriteBuffer(32 * 1024 * 1024)

	// Outbound Workers
	for i := 0; i < cores; i++ {
		go func() {
			for job := range outboundChan {
				stego := encode6Bit(job.payload, job.key, job.seq)
				conn.WriteToUDP(append([]byte{OP_DATA}, stego...), job.target)
				bufferPool.Put(stego[:cap(stego)])
			}
		}()
	}

	// Inbound Parallel Workers
	for i := 0; i < cores; i++ {
		go func() {
			for {
				buf := bufferPool.Get().([]byte)
				n, rem, err := conn.ReadFromUDP(buf)
				if err != nil {
					continue
				}

				switch buf[0] {
				case OP_DATA:
					var uKey []byte
					var sPtr *uint32
					if val, ok := mgr.ByAddr.Load(rem.String()); ok {
						s := val.(*UserSession)
						uKey, sPtr = s.UserKey, &s.SeqIn
						atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
					} else if !*isServer && myAssignedIP != "" {
						k := sha256.Sum256([]byte(basePass + myAssignedIP))
						uKey, sPtr = k[:], &serverSeq
					}

					if uKey != nil {
						if dec, ok := decode6Bit(buf[1:n], uKey, sPtr); ok {
							tun.Write(dec)
						}
					}
				case OP_AUTH:
					if *isServer {
						hwid := string(buf[1:n])
						newIP := fmt.Sprintf("10.0.0.%d", 2+atomic.AddInt64(&sessionCount, 1)-1)
						k := sha256.Sum256([]byte(basePass + newIP))
						s := &UserSession{Addr: rem, HWID: hwid, InternalIP: newIP, UserKey: k[:], LastSeen: time.Now().Unix()}
						mgr.ByIP.Store(newIP, s)
						mgr.ByHWID.Store(hwid, s)
						mgr.ByAddr.Store(rem.String(), s)
						conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(newIP)...), rem)
					} else {
						myAssignedIP = string(buf[1:n])
					}
				}
				bufferPool.Put(buf[:cap(buf)])
			}
		}()
	}

	target, _ := net.ResolveUDPAddr("udp", *tAddrStr)
	hwid := getHWID()
	go func() {
		for {
			if !*isServer && *tAddrStr != "" {
				if myAssignedIP == "" {
					conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(hwid)...), target)
				} else {
					conn.WriteToUDP([]byte{OP_HEARTBEAT}, target)
				}
			}
			time.Sleep(10 * time.Second)
		}
	}()

	pkt := make([]byte, 2048)
	for {
		n, err := tun.Read(pkt)
		if err != nil {
			continue
		}
		if *isServer {
			destIP := net.IP(pkt[16:20]).String()
			if val, ok := mgr.ByIP.Load(destIP); ok {
				u := val.(*UserSession)
				s := atomic.AddUint32(&u.SeqOut, 1) - 1
				outboundChan <- outboundJob{payload: append([]byte(nil), pkt[:n]...), target: u.Addr, seq: s, key: u.UserKey}
			}
		} else if myAssignedIP != "" {
			s := atomic.AddUint32(&clientSeq, 1) - 1
			k := sha256.Sum256([]byte(basePass + myAssignedIP))
			outboundChan <- outboundJob{payload: append([]byte(nil), pkt[:n]...), target: target, seq: s, key: k[:]}
		}
	}
}
