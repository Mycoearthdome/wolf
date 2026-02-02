package main

import (
	"crypto/sha256"
	"encoding/binary"
	"flag"
	"fmt"
	"math"
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
)

const (
	MagicSignature  uint32 = 0xACE1FACE
	TUN_MTU                = 1500
	BMP_HEADER_SIZE        = 1078
	OP_DATA         byte   = 4
	OP_AUTH         byte   = 5
	OP_HEARTBEAT    byte   = 6
	SESSION_TIMEOUT        = 180
)

type UserSession struct {
	Addr       *net.UDPAddr
	InternalIP string
	SeqIn      uint32 // Sequence from User to Server
	SeqOut     uint32 // Sequence from Server to User
	LastSeen   int64
	UserKey    string
}

type SessionManager struct {
	mu      sync.RWMutex
	ByIP    map[string]*UserSession
	ByAddr  map[string]*UserSession
	UsedIPs map[string]bool
}

var (
	mgr            = &SessionManager{ByIP: make(map[string]*UserSession), ByAddr: make(map[string]*UserSession), UsedIPs: make(map[string]bool)}
	conn           *net.UDPConn
	outboundChan   = make(chan outboundJob, 10000)
	inboundChan    = make(chan inboundJob, 10000)
	tunDevice      *water.Interface
	origForwarding string
	myAssignedIP   string
	basePass       string
	clientSeq      uint32 // Used by client to track outgoing packets
	serverSeq      uint32 // Used by client to track incoming packets from server
)

type outboundJob struct {
	payload []byte
	target  *net.UDPAddr
	seq     uint32
	key     string
}

type inboundJob struct {
	data []byte
	from *net.UDPAddr
}

// --- Stego Core ---

func deriveUserBaseKey(master, ip string) string {
	h := sha256.Sum256([]byte(master + ip))
	return fmt.Sprintf("%x", h)
}

func getPacketKey(userKey string, seq uint32) string {
	h := sha256.Sum256([]byte(fmt.Sprintf("%s-%d", userKey, seq)))
	return fmt.Sprintf("%x", h)
}

func xor(d []byte, p string) []byte {
	h := sha256.Sum256([]byte(p))
	rng := rand.New(rand.NewSource(int64(binary.BigEndian.Uint64(h[:8]))))
	res := make([]byte, len(d))
	for i := range d {
		res[i] = d[i] ^ uint8(rng.Intn(256))
	}
	return res
}

func encode(msg []byte, p string, seq uint32) []byte {
	payload := append(binary.BigEndian.AppendUint32(nil, MagicSignature), msg...)
	vault := xor(payload, p)
	dataLen := len(vault)
	side := int(math.Ceil(math.Sqrt(float64(16 + (dataLen * 2)))))
	bmp := make([]byte, BMP_HEADER_SIZE+(side*side))
	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[10:14], uint32(len(bmp))) // Proper BMP size field
	binary.LittleEndian.PutUint32(bmp[10:14], BMP_HEADER_SIZE)
	hdr := binary.BigEndian.AppendUint32(binary.BigEndian.AppendUint32(nil, uint32(dataLen)), seq)
	for i := 0; i < 16; i++ {
		bmp[BMP_HEADER_SIZE+i] = (bmp[BMP_HEADER_SIZE+i] & 0xF0) | ((hdr[i/2] >> (uint(i%2) * 4)) & 0x0F)
	}
	for i := 0; i < dataLen*2; i++ {
		bmp[BMP_HEADER_SIZE+16+i] = (bmp[BMP_HEADER_SIZE+16+i] & 0xF0) | ((vault[i/2] >> (uint(i%2) * 4)) & 0x0F)
	}
	return bmp
}

func decode(stego []byte, p string) ([]byte, uint32, bool) {
	if len(stego) < BMP_HEADER_SIZE+16 {
		return nil, 0, false
	}
	var hdr [8]byte
	for i := 0; i < 16; i++ {
		hdr[i/2] |= (stego[BMP_HEADER_SIZE+i] & 0x0F) << (uint(i%2) * 4)
	}
	vLen, seq := binary.BigEndian.Uint32(hdr[:4]), binary.BigEndian.Uint32(hdr[4:8])
	if vLen == 0 || vLen > 65000 {
		return nil, 0, false
	}
	vault := make([]byte, vLen)
	for i := 0; i < int(vLen)*2; i++ {
		off := BMP_HEADER_SIZE + 16 + i
		if off >= len(stego) {
			break
		}
		vault[i/2] |= (stego[off] & 0x0F) << (uint(i%2) * 4)
	}
	f := xor(vault, p)
	if len(f) > 4 && binary.BigEndian.Uint32(f[:4]) == MagicSignature {
		return f[4:], seq, true
	}
	return nil, 0, false
}

// --- System ---

func configureSystem(name, localIP, peerIP string, isServer bool) (string, string) {
	run := func(c string, args ...string) { _ = exec.Command(c, args...).Run() }
	getSys := func(k string) string {
		out, _ := exec.Command("sysctl", "-n", k).Output()
		return strings.TrimSpace(string(out))
	}
	run("ip", "addr", "flush", "dev", name)
	origForwarding = getSys("net.ipv4.ip_forward")

	out, _ := exec.Command("ip", "route", "show", "default").Output()
	fields := strings.Fields(string(out))
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
	run("ip", "addr", "replace", localIP+"/24", "dev", name)

	if isServer {
		run("sysctl", "-w", "net.ipv4.ip_forward=1")
		run("iptables", "-t", "nat", "-F")
		run("iptables", "-A", "FORWARD", "-i", name, "-j", "ACCEPT")
		run("iptables", "-A", "FORWARD", "-m state", "--state", "ESTABLISHED,RELATED", "-j", "ACCEPT")
		run("iptables", "-t", "nat", "-A", "POSTROUTING", "-o", dev, "-j", "MASQUERADE")
	} else if localIP != "0.0.0.0" {
		run("ip", "route", "add", peerIP, "via", gw, "dev", dev)
		run("ip", "route", "add", "0.0.0.0/1", "dev", name)
		run("ip", "route", "add", "128.0.0.0/1", "dev", name)
	}
	return gw, dev
}

func cleanup(name, peerIP, gw, dev string, isServer bool) {
	run := func(c string, args ...string) { _ = exec.Command(c, args...).Run() }
	fmt.Println("\n[*] Cleaning up...")
	run("sysctl", "-w", "net.ipv4.ip_forward="+origForwarding)
	run("iptables", "-t", "nat", "-F")
	run("iptables", "-D", "FORWARD", "-i", name, "-j", "ACCEPT")
	if !isServer && peerIP != "" {
		run("ip", "route", "del", peerIP)
	}
	os.Exit(0)
}

func main() {
	lPort := flag.String("l", "9000", "Port")
	tAddrStr := flag.String("t", "", "Target Server")
	flag.StringVar(&basePass, "p", "BatMan", "Key")
	tunIP := flag.String("ip", "10.0.0.1", "TUN IP")
	isServer := flag.Bool("server", false, "Server Mode")
	flag.Parse()

	numCPUs := runtime.NumCPU()
	runtime.GOMAXPROCS(numCPUs)

	lAddr, _ := net.ResolveUDPAddr("udp", "0.0.0.0:"+*lPort)
	conn, _ = net.ListenUDP("udp", lAddr)
	_ = conn.SetReadBuffer(128 * 1024 * 1024)
	_ = conn.SetWriteBuffer(128 * 1024 * 1024)

	tunDevice, _ = water.New(water.Config{DeviceType: water.TUN})
	pHost := ""
	if *tAddrStr != "" {
		pHost, _, _ = net.SplitHostPort(*tAddrStr)
	}

	startIP := *tunIP
	if !*isServer {
		startIP = "0.0.0.0"
	}
	gw, dev := configureSystem(tunDevice.Name(), startIP, pHost, *isServer)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGINT, syscall.SIGTERM)
	go func() { <-sig; cleanup(tunDevice.Name(), pHost, gw, dev, *isServer) }()

	// --- Multi-Core Workers ---
	for i := 0; i < numCPUs; i++ {
		go func() {
			for job := range outboundChan {
				stego := encode(job.payload, getPacketKey(job.key, job.seq), job.seq)
				conn.WriteToUDP(append([]byte{OP_DATA}, stego...), job.target)
			}
		}()
	}

	for i := 0; i < numCPUs; i++ {
		go func() {
			for job := range inboundChan {
				var uKey string
				var seqPtr *uint32
				if *isServer {
					mgr.mu.RLock()
					if s, ok := mgr.ByAddr[job.from.String()]; ok {
						uKey = s.UserKey
						seqPtr = &s.SeqIn // Track sequence coming FROM user
						atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
					}
					mgr.mu.RUnlock()
				} else {
					uKey = deriveUserBaseKey(basePass, myAssignedIP)
					seqPtr = &serverSeq // Client tracks sequence coming FROM server
				}

				if uKey != "" {
					curr := atomic.LoadUint32(seqPtr)
					for o := -20; o <= 20; o++ {
						searchSeq := uint32(int(curr) + o)
						if dec, s, ok := decode(job.data, getPacketKey(uKey, searchSeq)); ok {
							if s >= curr {
								atomic.StoreUint32(seqPtr, s+1)
							}
							tunDevice.Write(dec)
							break
						}
					}
				}
			}
		}()
	}

	// UDP Receiver
	go func() {
		for {
			buf := make([]byte, 65535)
			n, rem, err := conn.ReadFromUDP(buf)
			if err != nil {
				continue
			}
			op := buf[0]

			switch op {
			case OP_AUTH:
				if *isServer {
					mgr.mu.Lock()
					newIP := ""
					for i := 2; i < 254; i++ {
						c := fmt.Sprintf("10.0.0.%d", i)
						if !mgr.UsedIPs[c] {
							newIP = c
							break
						}
					}
					if newIP != "" {
						mgr.UsedIPs[newIP] = true
						mgr.ByIP[newIP] = &UserSession{Addr: rem, InternalIP: newIP, UserKey: deriveUserBaseKey(basePass, newIP), LastSeen: time.Now().Unix()}
						mgr.ByAddr[rem.String()] = mgr.ByIP[newIP]
						conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(newIP)...), rem)
					}
					mgr.mu.Unlock()
				} else {
					myAssignedIP = string(buf[1:n])
					configureSystem(tunDevice.Name(), myAssignedIP, pHost, false)
					fmt.Printf("[!] Browsing Ready: %s\n", myAssignedIP)
				}
			case OP_HEARTBEAT:
				if *isServer {
					mgr.mu.RLock()
					if s, ok := mgr.ByAddr[rem.String()]; ok {
						atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
					}
					mgr.mu.RUnlock()
				}
			case OP_DATA:
				inboundChan <- inboundJob{data: append([]byte(nil), buf[1:n]...), from: rem}
			}
		}
	}()

	// Heartbeat Loop
	go func() {
		target, _ := net.ResolveUDPAddr("udp", *tAddrStr)
		for {
			if !*isServer {
				if myAssignedIP == "" {
					conn.WriteToUDP([]byte{OP_AUTH}, target)
				} else {
					conn.WriteToUDP([]byte{OP_HEARTBEAT}, target)
				}
			}
			time.Sleep(10 * time.Second)
		}
	}()

	fmt.Printf("[!] Engine Active (%d Cores)\n", numCPUs)

	// --- TUN Reader ---
	pkt := make([]byte, 4096)
	for {
		n, err := tunDevice.Read(pkt)
		if err != nil {
			break
		}

		if *isServer {
			destIP := net.IP(pkt[16:20]).String()
			mgr.mu.RLock()
			u, ok := mgr.ByIP[destIP]
			mgr.mu.RUnlock()
			if ok {
				s := atomic.AddUint32(&u.SeqOut, 1) - 1 // Server uses SeqOut for internet -> user
				outboundChan <- outboundJob{payload: append([]byte(nil), pkt[:n]...), target: u.Addr, seq: s, key: u.UserKey}
			}
		} else if myAssignedIP != "" {
			t, _ := net.ResolveUDPAddr("udp", *tAddrStr)
			s := atomic.AddUint32(&clientSeq, 1) - 1 // Client uses clientSeq for user -> server
			outboundChan <- outboundJob{payload: append([]byte(nil), pkt[:n]...), target: t, seq: s, key: deriveUserBaseKey(basePass, myAssignedIP)}
		}
	}
}
