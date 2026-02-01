package main

import (
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"encoding/binary"
	"flag"
	"fmt"
	"io"
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
	TUN_MTU                = 1400
	BMP_HEADER_SIZE        = 1078
)

var (
	state          *SessionState
	conn           *net.UDPConn
	tAddr          *net.UDPAddr
	tMu            sync.RWMutex
	encryptChan    = make(chan encryptJob, 4096)
	tunDevice      *water.Interface
	keyCache       = make(map[uint32]string)
	cacheMu        sync.RWMutex
	origForwarding string
	origFragHigh   string
	origFragLow    string
	origFragTime   string
	lastSeen       int64 // Atomic timestamp
)

type encryptJob struct {
	payload []byte
	seq     uint32
}

type SessionState struct {
	BasePass string
	Seq      uint32
}

// --- Stego & Crypto Logic ---

func getKeys(basePass string, seq uint32) string {
	cacheMu.RLock()
	if val, ok := keyCache[seq]; ok {
		cacheMu.RUnlock()
		return val
	}
	cacheMu.RUnlock()
	h := sha256.Sum256([]byte(fmt.Sprintf("%s-%d", basePass, seq)))
	pass := fmt.Sprintf("%x", h)
	cacheMu.Lock()
	keyCache[seq] = pass
	if len(keyCache) > 5000 {
		keyCache = make(map[uint32]string)
	}
	cacheMu.Unlock()
	return pass
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
	var b bytes.Buffer
	zw := gzip.NewWriter(&b)
	zw.Write(msg)
	zw.Close()
	payload := append(binary.BigEndian.AppendUint32(nil, MagicSignature), b.Bytes()...)
	vault := xor(payload, p)
	dataLen := len(vault)
	pixelCount := 16 + (dataLen * 2)
	side := int(math.Ceil(math.Sqrt(float64(pixelCount))))
	if side < 1 {
		side = 1
	}
	bmp := make([]byte, BMP_HEADER_SIZE+(side*side))
	copy(bmp[0:2], "BM")
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
		zr, _ := gzip.NewReader(bytes.NewReader(f[4:]))
		if zr != nil {
			dec, _ := io.ReadAll(zr)
			return dec, seq, true
		}
	}
	return nil, 0, false
}

// --- Resilience Logic ---

func sendControlPacket(op byte, target *net.UDPAddr, secret string, seq uint32) {
	h := sha256.New()
	h.Write([]byte(fmt.Sprintf("%s-%d-%d", secret, op, seq)))
	sig := h.Sum(nil)
	pkt := append([]byte{op}, binary.BigEndian.AppendUint32(nil, seq)...)
	pkt = append(pkt, sig...)
	conn.WriteToUDP(pkt, target)
}

func verifyControl(pkt []byte, secret string) (byte, uint32, bool) {
	if len(pkt) < 37 {
		return 0, 0, false
	}
	op := pkt[0]
	seq := binary.BigEndian.Uint32(pkt[1:5])
	h := sha256.New()
	h.Write([]byte(fmt.Sprintf("%s-%d-%d", secret, op, seq)))
	return op, seq, bytes.Equal(pkt[5:37], h.Sum(nil))
}

// --- System ---

func configureSystem(name, localIP, peerIP string, isServer bool) (string, string) {
	run := func(c string, args ...string) { _ = exec.Command(c, args...).Run() }
	getSys := func(k string) string {
		out, _ := exec.Command("sysctl", "-n", k).Output()
		return strings.TrimSpace(string(out))
	}
	origForwarding = getSys("net.ipv4.ip_forward")
	origFragHigh = getSys("net.ipv4.ipfrag_high_thresh")
	origFragLow = getSys("net.ipv4.ipfrag_low_thresh")
	origFragTime = getSys("net.ipv4.ipfrag_time")
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
	run("ip", "addr", "add", localIP+"/24", "dev", name)
	run("iptables", "-t", "mangle", "-A", "FORWARD", "-p", "tcp", "--tcp-flags", "SYN,RST", "SYN", "-j", "TCPMSS", "--clamp-mss-to-pmtu")
	run("sysctl", "-w", "net.ipv4.ipfrag_high_thresh=134217728")
	run("sysctl", "-w", "net.ipv4.ipfrag_low_thresh=100663296")
	run("sysctl", "-w", "net.ipv4.ipfrag_time=60")
	if !isServer {
		run("ip", "route", "add", peerIP, "via", gw, "dev", dev)
		run("ip", "route", "add", "0.0.0.0/1", "dev", name)
		run("ip", "route", "add", "128.0.0.0/1", "dev", name)
	} else {
		run("sysctl", "-w", "net.ipv4.ip_forward=1")
		run("iptables", "-P", "FORWARD", "ACCEPT")
		run("iptables", "-t", "nat", "-A", "POSTROUTING", "-o", dev, "-j", "MASQUERADE")
	}
	return gw, dev
}

func cleanup(name, peerIP, gw, dev string, isServer bool) {
	run := func(c string, args ...string) { _ = exec.Command(c, args...).Run() }
	fmt.Println("\n[*] Restoring system...")
	run("sysctl", "-w", "net.ipv4.ip_forward="+origForwarding)
	run("sysctl", "-w", "net.ipv4.ipfrag_high_thresh="+origFragHigh)
	run("sysctl", "-w", "net.ipv4.ipfrag_low_thresh="+origFragLow)
	run("sysctl", "-w", "net.ipv4.ipfrag_time="+origFragTime)
	run("iptables", "-t", "mangle", "-F")
	if isServer {
		run("iptables", "-t", "nat", "-F")
	} else {
		run("ip", "route", "del", peerIP)
	}
	os.Exit(0)
}

func main() {
	lPort := flag.String("l", "9000", "Listen Port")
	tAddrStr := flag.String("t", "", "Peer IP:Port")
	pass := flag.String("p", "shibboleth", "Secret Key")
	tunIP := flag.String("ip", "10.0.0.1", "Local TUN IP")
	isServer := flag.Bool("server", false, "Server Mode")
	flag.Parse()

	state = &SessionState{BasePass: *pass}
	lAddr, _ := net.ResolveUDPAddr("udp", "0.0.0.0:"+*lPort)
	conn, _ = net.ListenUDP("udp", lAddr)
	_ = conn.SetReadBuffer(64 * 1024 * 1024)
	_ = conn.SetWriteBuffer(64 * 1024 * 1024)

	if *tAddrStr != "" {
		tAddr, _ = net.ResolveUDPAddr("udp", *tAddrStr)
	}
	tunDevice, _ = water.New(water.Config{DeviceType: water.TUN})
	pHost := ""
	if *tAddrStr != "" {
		pHost, _, _ = net.SplitHostPort(*tAddrStr)
	}
	gw, dev := configureSystem(tunDevice.Name(), *tunIP, pHost, *isServer)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGINT, syscall.SIGTERM)
	go func() { <-sig; cleanup(tunDevice.Name(), pHost, gw, dev, *isServer) }()

	// KeepAlive & Dead-Man Switch
	go func() {
		atomic.StoreInt64(&lastSeen, time.Now().Unix())
		for {
			tMu.RLock()
			target := tAddr
			tMu.RUnlock()
			if target != nil {
				curr := atomic.LoadUint32(&state.Seq)

				// Dead-Man Switch Logic
				ls := atomic.LoadInt64(&lastSeen)
				if time.Now().Unix()-ls > 30 {
					fmt.Println("[!] Connection Stalled. Triggering Resync...")
					sendControlPacket(1, target, state.BasePass, curr) // Force Sync
					atomic.StoreInt64(&lastSeen, time.Now().Unix())
				} else {
					sendControlPacket(2, target, state.BasePass, curr) // Heartbeat
				}
			}
			time.Sleep(10 * time.Second)
		}
	}()

	// Receiver
	go func() {
		for {
			buf := make([]byte, 65535)
			n, rem, err := conn.ReadFromUDP(buf)
			if err != nil {
				continue
			}
			tMu.Lock()
			tAddr = rem
			tMu.Unlock()
			atomic.StoreInt64(&lastSeen, time.Now().Unix())

			op := buf[0]
			if op == 1 || op == 2 {
				if _, nS, ok := verifyControl(buf[:n], state.BasePass); ok {
					curr := atomic.LoadUint32(&state.Seq)
					if nS > curr || op == 1 {
						atomic.StoreUint32(&state.Seq, nS)
						if op == 1 {
							fmt.Printf("[!] PEER RECOVERED. Seq set to: %d\n", nS)
						}
					}
				}
			} else if op == 4 {
				go func(stego []byte) {
					curr := atomic.LoadUint32(&state.Seq)
					for o := -20; o <= 20; o++ {
						p := getKeys(state.BasePass, uint32(int(curr)+o))
						if dec, s, ok := decode(stego, p); ok {
							if s >= curr {
								atomic.StoreUint32(&state.Seq, s+1)
							}
							tunDevice.Write(dec)
							return
						}
					}
				}(buf[1:n])
			}
		}
	}()

	// Worker Pool
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for job := range encryptChan {
				p := getKeys(state.BasePass, job.seq)
				stego := encode(job.payload, p, job.seq)
				tMu.RLock()
				target := tAddr
				tMu.RUnlock()
				if target != nil {
					conn.WriteToUDP(append([]byte{4}, stego...), target)
				}
			}
		}()
	}

	fmt.Println("[!] Turbo-Stego VPN Operational.")
	pkt := make([]byte, TUN_MTU)
	for {
		n, err := tunDevice.Read(pkt)
		if err != nil {
			break
		}
		s := atomic.AddUint32(&state.Seq, 1) - 1
		select {
		case encryptChan <- encryptJob{payload: append([]byte(nil), pkt[:n]...), seq: s}:
		default:
		}
	}
}
