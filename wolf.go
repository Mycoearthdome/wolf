package main

import (
	"crypto/cipher"
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
	"golang.org/x/crypto/chacha20poly1305"
)

// --- Constants & Config ---

const (
	TUN_MTU     = 1350
	HDR_SIZE    = 1  // OpCode
	NONCE_SIZE  = 12 // ChaCha20 Nonce (4-byte Salt + 8-byte Seq)
	TAG_SIZE    = 16 // Poly1305 MAC
	OVERHEAD    = HDR_SIZE + NONCE_SIZE + TAG_SIZE
	WINDOW_SIZE = 64
	SESSION_TTL = 300 // 5 minutes
)

const (
	OP_DATA uint8 = iota + 4
	OP_AUTH
	OP_KEEPALIVE
)

// --- Session & Security Types ---

type UserSession struct {
	Addr       *net.UDPAddr
	HWID       string
	InternalIP string
	SeqOut     uint64
	LastSeen   int64
	AEAD       cipher.AEAD

	// Anti-Replay Sliding Window
	mu        sync.Mutex
	lastSeqIn uint64
	window    uint64
}

func (s *UserSession) VerifySeq(seq uint64) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	if seq <= s.lastSeqIn {
		diff := s.lastSeqIn - seq
		if diff >= WINDOW_SIZE || (s.window>>diff)&1 == 1 {
			return false
		}
		s.window |= (1 << diff)
		return true
	}
	diff := seq - s.lastSeqIn
	if diff >= WINDOW_SIZE {
		s.window = 1
	} else {
		s.window = (s.window << diff) | 1
	}
	s.lastSeqIn = seq
	return true
}

type SessionManager struct {
	ByIP   sync.Map
	ByAddr sync.Map
	ByHWID sync.Map
}

// --- Global State ---

var (
	mgr            = &SessionManager{}
	conn           *net.UDPConn
	origForwarding string
	myAssignedIP   string
	clientAEAD     atomic.Value
	clientSeq      uint64
	sessionCount   int64
	lastActivity   int64
	securityLock   sync.RWMutex
	banList        = make(map[string]int64)
	bufferPool     = sync.Pool{
		New: func() interface{} { return make([]byte, 2048) },
	}
)

// --- Crypto Helpers ---

func sealPacket(dst []byte, aead cipher.AEAD, seq uint64, payload []byte) []byte {
	nonce := dst[HDR_SIZE : HDR_SIZE+NONCE_SIZE]
	binary.BigEndian.PutUint32(nonce[:4], 0xDEADBEEF) // Salt
	binary.BigEndian.PutUint64(nonce[4:], seq)
	return aead.Seal(dst[:HDR_SIZE+NONCE_SIZE], nonce, payload, nil)
}

func openPacket(raw []byte, aead cipher.AEAD) ([]byte, uint64, error) {
	if len(raw) < OVERHEAD {
		return nil, 0, fmt.Errorf("short")
	}
	nonce := raw[HDR_SIZE : HDR_SIZE+NONCE_SIZE]
	seq := binary.BigEndian.Uint64(nonce[4:])
	out, err := aead.Open(nil, nonce, raw[HDR_SIZE+NONCE_SIZE:], nil)
	return out, seq, err
}

// --- System Network Config ---

func runCmd(c string, args ...string) { _ = exec.Command(c, args...).Run() }

func configureSystem(name, localIP, peerIP string, isServer bool) (string, string) {
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

	runCmd("ip", "link", "set", "dev", name, "up", "mtu", fmt.Sprintf("%d", TUN_MTU))
	if localIP != "0.0.0.0" {
		runCmd("ip", "addr", "replace", localIP+"/24", "dev", name)
	}

	if isServer {
		runCmd("sysctl", "-w", "net.ipv4.ip_forward=1")
		runCmd("iptables", "-t", "nat", "-A", "POSTROUTING", "-o", dev, "-j", "MASQUERADE")
		runCmd("iptables", "-t", "mangle", "-A", "FORWARD", "-p", "tcp", "--tcp-flags", "SYN,RST", "SYN", "-j", "TCPMSS", "--set-mss", "1260")
		runCmd("iptables", "-A", "FORWARD", "-i", name, "-o", dev, "-j", "ACCEPT")
		runCmd("iptables", "-A", "FORWARD", "-i", dev, "-o", name, "-m", "state", "--state", "RELATED,ESTABLISHED", "-j", "ACCEPT")
	} else if localIP != "0.0.0.0" && peerIP != "" {
		runCmd("ip", "route", "add", peerIP, "via", gw, "dev", dev, "metric", "1")
		_ = exec.Command("mv", "/etc/resolv.conf", "/etc/resolv.conf.bak").Run()
		_ = exec.Command("bash", "-c", "echo 'nameserver 8.8.8.8' > /etc/resolv.conf").Run()

		runCmd("iptables", "-N", "VPN_KILLSWITCH")
		runCmd("iptables", "-I", "OUTPUT", "1", "-j", "VPN_KILLSWITCH")
		runCmd("iptables", "-A", "VPN_KILLSWITCH", "-o", "lo", "-j", "ACCEPT")
		runCmd("iptables", "-A", "VPN_KILLSWITCH", "-d", peerIP, "-p", "udp", "-j", "ACCEPT")
		runCmd("iptables", "-A", "VPN_KILLSWITCH", "-p", "udp", "--dport", "53", "-j", "ACCEPT")
		runCmd("iptables", "-A", "VPN_KILLSWITCH", "-o", name, "-j", "ACCEPT")
		runCmd("iptables", "-A", "VPN_KILLSWITCH", "-j", "DROP")

		runCmd("ip", "route", "add", "0.0.0.0/1", "dev", name, "metric", "5")
		runCmd("ip", "route", "add", "128.0.0.0/1", "dev", name, "metric", "5")
	}
	return gw, dev
}

func cleanup(origFwd string, isServer bool) {
	fmt.Println("\n[*] Cleaning up networking and security rules...")
	securityLock.Lock()
	for ip := range banList {
		runCmd("iptables", "-D", "INPUT", "-s", ip, "-j", "DROP")
	}
	securityLock.Unlock()

	if isServer {
		runCmd("iptables", "-t", "nat", "-D", "POSTROUTING", "1")
		runCmd("iptables", "-D", "FORWARD", "-m", "state", "--state", "RELATED,ESTABLISHED", "-j", "ACCEPT")
	} else {
		runCmd("iptables", "-D", "OUTPUT", "-j", "VPN_KILLSWITCH")
		runCmd("iptables", "-F", "VPN_KILLSWITCH")
		runCmd("iptables", "-X", "VPN_KILLSWITCH")
		if _, err := os.Stat("/etc/resolv.conf.bak"); err == nil {
			_ = exec.Command("mv", "/etc/resolv.conf.bak", "/etc/resolv.conf").Run()
		}
	}
	runCmd("sysctl", "-w", "net.ipv4.ip_forward="+origFwd)
	fmt.Println("[+] Cleanup complete. Exiting.")
	os.Exit(0)
}

// --- Main Engine ---

func main() {
	lPort := flag.String("l", "9000", "Port")
	tAddrStr := flag.String("t", "", "Target")
	pass := flag.String("p", "BatMan", "Secret")
	tunIP := flag.String("ip", "10.0.0.1", "Internal IP")
	isServer := flag.Bool("server", false, "Server Mode")
	flag.Parse()

	runtime.GOMAXPROCS(runtime.NumCPU())
	tun, _ := water.New(water.Config{DeviceType: water.TUN})

	pHost := ""
	if *tAddrStr != "" {
		pHost, _, _ = net.SplitHostPort(*tAddrStr)
	}
	configureSystem(tun.Name(), *tunIP, pHost, *isServer)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGINT, syscall.SIGTERM)
	go func() {
		<-sig
		cleanup(origForwarding, *isServer)
	}()

	lAddr, _ := net.ResolveUDPAddr("udp", ":"+*lPort)
	conn, _ = net.ListenUDP("udp", lAddr)

	target, _ := net.ResolveUDPAddr("udp", *tAddrStr)
	host, _ := os.Hostname()

	// Reaper for Server
	if *isServer {
		go func() {
			for range time.Tick(30 * time.Second) {
				now := time.Now().Unix()
				mgr.ByHWID.Range(func(k, v interface{}) bool {
					s := v.(*UserSession)
					if now-atomic.LoadInt64(&s.LastSeen) > SESSION_TTL {
						mgr.ByHWID.Delete(k)
						mgr.ByAddr.Delete(s.Addr.String())
						mgr.ByIP.Delete(s.InternalIP)
					}
					return true
				})
			}
		}()
	}

	// 1. Inbound Workers: UDP -> TUN
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for {
				buf := bufferPool.Get().([]byte)
				n, rem, err := conn.ReadFromUDP(buf)
				if err != nil {
					bufferPool.Put(buf)
					continue
				}

				switch buf[0] {
				case OP_DATA:
					var aead cipher.AEAD
					var session *UserSession
					if *isServer {
						if val, ok := mgr.ByAddr.Load(rem.String()); ok {
							session = val.(*UserSession)
							aead = session.AEAD
						}
					} else {
						if val := clientAEAD.Load(); val != nil {
							aead = val.(cipher.AEAD)
						}
					}

					if aead != nil {
						plain, seq, err := openPacket(buf[:n], aead)
						if err == nil {
							if !*isServer || session.VerifySeq(seq) {
								tun.Write(plain)
								if *isServer {
									atomic.StoreInt64(&session.LastSeen, time.Now().Unix())
								} else {
									atomic.StoreInt64(&lastActivity, time.Now().Unix())
								}
							}
						}
					}
				case OP_AUTH:
					if *isServer {
						hwid := string(buf[1:n])
						var s *UserSession
						if val, ok := mgr.ByHWID.Load(hwid); ok {
							s = val.(*UserSession)
							mgr.ByAddr.Delete(s.Addr.String())
							s.Addr = rem
						} else {
							newIP := fmt.Sprintf("10.0.0.%d", 2+atomic.AddInt64(&sessionCount, 1)-1)
							key := sha256.Sum256([]byte(*pass + newIP))
							c, _ := chacha20poly1305.New(key[:])
							s = &UserSession{Addr: rem, HWID: hwid, InternalIP: newIP, AEAD: c}
							mgr.ByHWID.Store(hwid, s)
							mgr.ByIP.Store(newIP, s)
						}
						mgr.ByAddr.Store(rem.String(), s)
						atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
						conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(s.InternalIP)...), rem)
					} else {
						myAssignedIP = string(buf[1:n])
						key := sha256.Sum256([]byte(*pass + myAssignedIP))
						c, _ := chacha20poly1305.New(key[:])
						clientAEAD.Store(c)
						runCmd("ip", "addr", "replace", myAssignedIP+"/24", "dev", tun.Name())
						atomic.StoreInt64(&lastActivity, time.Now().Unix())
					}
				case OP_KEEPALIVE:
					if *isServer {
						if val, ok := mgr.ByAddr.Load(rem.String()); ok {
							atomic.StoreInt64(&val.(*UserSession).LastSeen, time.Now().Unix())
						}
					} else {
						atomic.StoreInt64(&lastActivity, time.Now().Unix())
					}
				}
				bufferPool.Put(buf)
			}
		}()
	}

	// 2. Heartbeat
	go func() {
		for range time.Tick(10 * time.Second) {
			if !*isServer && *tAddrStr != "" {
				if time.Now().Unix()-atomic.LoadInt64(&lastActivity) > 30 || myAssignedIP == "" {
					conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(host)...), target)
				} else {
					conn.WriteToUDP([]byte{OP_KEEPALIVE}, target)
				}
			}
		}
	}()

	// 3. Outbound Loop: TUN -> UDP
	for {
		pkt := bufferPool.Get().([]byte)
		n, err := tun.Read(pkt)
		if err != nil {
			bufferPool.Put(pkt)
			continue
		}

		txBuf := bufferPool.Get().([]byte)
		txBuf[0] = OP_DATA
		if *isServer {
			if n >= 20 {
				destIP := net.IP(pkt[16:20]).String()
				if val, ok := mgr.ByIP.Load(destIP); ok {
					u := val.(*UserSession)
					conn.WriteToUDP(sealPacket(txBuf, u.AEAD, atomic.AddUint64(&u.SeqOut, 1), pkt[:n]), u.Addr)
				}
			}
		} else if val := clientAEAD.Load(); val != nil {
			conn.WriteToUDP(sealPacket(txBuf, val.(cipher.AEAD), atomic.AddUint64(&clientSeq, 1), pkt[:n]), target)
		}
		bufferPool.Put(pkt)
		bufferPool.Put(txBuf)
	}
}
