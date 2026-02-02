package main

import (
	"crypto/sha256"
	"encoding/binary"
	"flag"
	"fmt"
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
	MagicSignature  uint32 = 0xACE1FACE
	TUN_MTU                = 680
	BMP_HEADER_SIZE        = 54
	OP_DATA         byte   = 4
	OP_AUTH         byte   = 5
	OP_HEARTBEAT    byte   = 6
	SESSION_TIMEOUT        = 300
)

// --- Helper: Generate HWID ---
func getHWID() string {
	host, _ := os.Hostname()
	// Quick hash of hostname for identity
	h := sha256.Sum256([]byte(host))
	return fmt.Sprintf("%x", h[:8])
}

// --- Sliding Window Logic ---
type ReplayWindow struct {
	mu     sync.Mutex
	maxSeq uint32
	mask   uint64
}

func (rw *ReplayWindow) Verify(seq uint32) bool {
	rw.mu.Lock()
	defer rw.mu.Unlock()
	if seq > rw.maxSeq {
		shift := seq - rw.maxSeq
		if shift >= 64 {
			rw.mask = 1
		} else {
			rw.mask = (rw.mask << shift) | 1
		}
		rw.maxSeq = seq
		return true
	}
	diff := rw.maxSeq - seq
	if diff >= 64 || (rw.mask>>diff&1) != 0 {
		return false
	}
	rw.mask |= (1 << diff)
	return true
}

// --- Session Logic ---
type UserSession struct {
	Addr       *net.UDPAddr
	HWID       string
	InternalIP string
	Window     *ReplayWindow
	SeqOut     uint32
	LastSeen   int64
	UserKey    []byte
}

type SessionManager struct {
	mu      sync.RWMutex
	ByIP    map[string]*UserSession
	ByAddr  map[string]*UserSession
	ByHWID  map[string]*UserSession
	UsedIPs map[string]bool
}

var (
	mgr            = &SessionManager{ByIP: make(map[string]*UserSession), ByAddr: make(map[string]*UserSession), ByHWID: make(map[string]*UserSession), UsedIPs: make(map[string]bool)}
	conn           *net.UDPConn
	outboundChan   = make(chan outboundJob, 20000)
	inboundChan    = make(chan inboundJob, 20000)
	tunDevice      *water.Interface
	origForwarding string
	myAssignedIP   string
	basePass       string
	clientSeq      uint32
	clientWindow   = &ReplayWindow{}
)

type outboundJob struct {
	payload []byte
	target  *net.UDPAddr
	seq     uint32
	key     []byte
}

type inboundJob struct {
	data []byte
	from *net.UDPAddr
}

// --- Stego & Crypto Core ---
func deriveUserBaseKey(master, ip string) []byte {
	h := sha256.Sum256([]byte(master + ip))
	return h[:]
}

func fastCrypt(data []byte, key []byte, seq uint32) {
	var nonce [chacha20.NonceSize]byte
	binary.LittleEndian.PutUint32(nonce[0:4], seq)
	c, _ := chacha20.NewUnauthenticatedCipher(key, nonce[:])
	c.XORKeyStream(data, data)
}

func encode(msg []byte, key []byte, seq uint32) []byte {
	vault := make([]byte, 4+len(msg))
	binary.BigEndian.PutUint32(vault[0:4], MagicSignature)
	copy(vault[4:], msg)
	fastCrypt(vault, key, seq)
	dataLen := len(vault)
	payloadArea := 16 + (dataLen * 2)
	bmp := make([]byte, BMP_HEADER_SIZE+payloadArea)
	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[2:6], uint32(len(bmp)))
	binary.LittleEndian.PutUint32(bmp[10:14], uint32(BMP_HEADER_SIZE))
	binary.LittleEndian.PutUint32(bmp[14:18], 40)
	binary.LittleEndian.PutUint32(bmp[18:22], uint32(payloadArea/3))
	binary.LittleEndian.PutUint32(bmp[22:26], 1)
	binary.LittleEndian.PutUint16(bmp[26:28], 1)
	binary.LittleEndian.PutUint16(bmp[28:30], 24)
	hdr := make([]byte, 8)
	binary.BigEndian.PutUint32(hdr[0:4], uint32(dataLen))
	binary.BigEndian.PutUint32(hdr[4:8], seq)
	for i := 0; i < 16; i++ {
		bmp[BMP_HEADER_SIZE+i] = (bmp[BMP_HEADER_SIZE+i] & 0xF0) | ((hdr[i/2] >> (uint(i%2) * 4)) & 0x0F)
	}
	for i := 0; i < dataLen*2; i++ {
		bmp[BMP_HEADER_SIZE+16+i] = (bmp[BMP_HEADER_SIZE+16+i] & 0xF0) | ((vault[i/2] >> (uint(i%2) * 4)) & 0x0F)
	}
	return bmp
}

func decode(stego []byte, key []byte, window *ReplayWindow) ([]byte, bool) {
	if len(stego) < BMP_HEADER_SIZE+16 {
		return nil, false
	}
	var hdr [8]byte
	for i := 0; i < 16; i++ {
		hdr[i/2] |= (stego[BMP_HEADER_SIZE+i] & 0x0F) << (uint(i%2) * 4)
	}
	vLen := binary.BigEndian.Uint32(hdr[0:4])
	seq := binary.BigEndian.Uint32(hdr[4:8])
	if vLen == 0 || vLen > 1500 || !window.Verify(seq) {
		return nil, false
	}
	vault := make([]byte, vLen)
	for i := 0; i < int(vLen)*2; i++ {
		vault[i/2] |= (stego[BMP_HEADER_SIZE+16+i] & 0x0F) << (uint(i%2) * 4)
	}
	fastCrypt(vault, key, seq)
	if binary.BigEndian.Uint32(vault[0:4]) == MagicSignature {
		return vault[4:], true
	}
	return nil, false
}

// --- System ---
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
		if f == f && f == "dev" {
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
		run("iptables", "-t", "mangle", "-A", "FORWARD", "-p", "tcp", "--tcp-flags", "SYN,RST", "SYN", "-j", "TCPMSS", "--set-mss", "600")
	} else if localIP != "0.0.0.0" && peerIP != "" {
		run("ip", "route", "add", peerIP, "via", gw, "dev", dev)
		run("ip", "route", "add", "0.0.0.0/1", "dev", name)
		run("ip", "route", "add", "128.0.0.0/1", "dev", name)
	}
	return gw, dev
}

func cleanup(name, peerIP, gw, dev string, isServer bool) {
	run := func(c string, args ...string) { _ = exec.Command(c, args...).Run() }
	run("sysctl", "-w", "net.ipv4.ip_forward="+origForwarding)
	run("iptables", "-t", "nat", "-F")
	run("iptables", "-t", "mangle", "-F")
	os.Exit(0)
}

func main() {
	lPort := flag.String("l", "9000", "UDP Port")
	tAddrStr := flag.String("t", "", "Target Host")
	flag.StringVar(&basePass, "p", "BatMan", "Key")
	tunIP := flag.String("ip", "10.0.0.1", "TUN IP")
	isServer := flag.Bool("server", false, "Server Mode")
	flag.Parse()

	runtime.GOMAXPROCS(runtime.NumCPU())
	tun, _ := water.New(water.Config{DeviceType: water.TUN})
	pHost := ""
	if *tAddrStr != "" {
		pHost, _, _ = net.SplitHostPort(*tAddrStr)
	}
	gw, dev := configureSystem(tun.Name(), *tunIP, pHost, *isServer)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGINT, syscall.SIGTERM)
	go func() { <-sig; cleanup(tun.Name(), pHost, gw, dev, *isServer) }()

	lAddr, _ := net.ResolveUDPAddr("udp", ":"+*lPort)
	conn, _ = net.ListenUDP("udp", lAddr)

	// Dashboard
	go func() {
		for {
			time.Sleep(2 * time.Second)
			fmt.Printf("\033[H\033[J")
			fmt.Printf("=== WOLF VPN DASHBOARD (%s) ===\n", getHWID())
			if *isServer {
				mgr.mu.RLock()
				fmt.Printf("Active Clients: %d\n", len(mgr.ByIP))
				for ip, s := range mgr.ByIP {
					fmt.Printf("[%s] HWID:%s | Last:%v | InMax:%d | Out:%d\n", ip, s.HWID, time.Since(time.Unix(s.LastSeen, 0)).Truncate(time.Second), s.Window.maxSeq, s.SeqOut)
				}
				mgr.mu.RUnlock()
			} else {
				fmt.Printf("Assigned IP: %s\n", myAssignedIP)
				fmt.Printf("Inbound Max Seq: %d | Outbound Seq: %d\n", clientWindow.maxSeq, clientSeq)
			}
		}
	}()

	// Workers
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for job := range outboundChan {
				stego := encode(job.payload, job.key, job.seq)
				conn.WriteToUDP(append([]byte{OP_DATA}, stego...), job.target)
			}
		}()
		go func() {
			for job := range inboundChan {
				var uKey []byte
				var win *ReplayWindow
				mgr.mu.RLock()
				if s, ok := mgr.ByAddr[job.from.String()]; ok {
					uKey, win = s.UserKey, s.Window
					atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
				} else if !*isServer && myAssignedIP != "" {
					uKey, win = deriveUserBaseKey(basePass, myAssignedIP), clientWindow
				}
				mgr.mu.RUnlock()
				if uKey != nil {
					if dec, ok := decode(job.data, uKey, win); ok {
						tun.Write(dec)
					}
				}
			}
		}()
	}

	// UDP Handler
	go func() {
		buf := make([]byte, 65535)
		for {
			n, rem, _ := conn.ReadFromUDP(buf)
			switch buf[0] {
			case OP_AUTH:
				if *isServer {
					id := string(buf[1:n])
					mgr.mu.Lock()
					s, exists := mgr.ByHWID[id]
					if !exists {
						newIP := fmt.Sprintf("10.0.0.%d", len(mgr.ByIP)+2)
						s = &UserSession{Addr: rem, HWID: id, InternalIP: newIP, Window: &ReplayWindow{}, UserKey: deriveUserBaseKey(basePass, newIP), LastSeen: time.Now().Unix()}
						mgr.ByIP[newIP] = s
						mgr.ByHWID[id] = s
					}
					s.Addr = rem // Update physical address if it changed
					mgr.ByAddr[rem.String()] = s
					mgr.mu.Unlock()
					conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(s.InternalIP)...), rem)
				} else {
					myAssignedIP = string(buf[1:n])
				}
			case OP_DATA:
				inboundChan <- inboundJob{data: append([]byte(nil), buf[1:n]...), from: rem}
			case OP_HEARTBEAT:
				mgr.mu.RLock()
				if s, ok := mgr.ByAddr[rem.String()]; ok {
					atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
				}
				mgr.mu.RUnlock()
			}
		}
	}()

	// Heartbeat / Auth
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

	pkt := make([]byte, 4096)
	for {
		n, _ := tun.Read(pkt)
		if *isServer {
			destIP := net.IP(pkt[16:20]).String()
			mgr.mu.RLock()
			u, ok := mgr.ByIP[destIP]
			mgr.mu.RUnlock()
			if ok {
				s := atomic.AddUint32(&u.SeqOut, 1) - 1
				outboundChan <- outboundJob{payload: append([]byte(nil), pkt[:n]...), target: u.Addr, seq: s, key: u.UserKey}
			}
		} else if myAssignedIP != "" {
			s := atomic.AddUint32(&clientSeq, 1) - 1
			outboundChan <- outboundJob{payload: append([]byte(nil), pkt[:n]...), target: target, seq: s, key: deriveUserBaseKey(basePass, myAssignedIP)}
		}
	}
}
