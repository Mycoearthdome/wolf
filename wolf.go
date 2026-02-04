package main

import (
	"crypto/cipher"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"flag"
	"fmt"
	"io"
	"net"
	"net/http"
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
	"golang.org/x/crypto/curve25519"
)

// --- Constants ---
const (
	TUN_MTU     = 1350
	OVERHEAD    = 1 + 12 + 16
	WINDOW_SIZE = 64
	SESSION_TTL = 300 // 5 Minutes of inactivity triggers the Reaper
	UPNP_LEASE  = 3600
)

const (
	OP_DATA uint8 = iota + 4
	OP_AUTH
	OP_KEEPALIVE
)

type UserSession struct {
	Addr       *net.UDPAddr
	InternalIP string
	SeqOut     uint64
	LastSeen   int64
	AEAD       cipher.AEAD
	mu         sync.Mutex
	lastSeqIn  uint64
	window     uint64
}

type SessionManager struct {
	ByIdentity sync.Map
	ByAddr     sync.Map
	ByIP       sync.Map
}

var (
	startTime      = time.Now()
	mgr            = &SessionManager{}
	conn           *net.UDPConn
	origForwarding string
	clientAEAD     atomic.Value
	clientSeq      uint64
	lastActivity   int64
	bufferPool     = sync.Pool{New: func() interface{} { return make([]byte, 2048) }}
)

// --- Helper Functions ---

func runCmd(c string, args ...string) { _ = exec.Command(c, args...).Run() }

func generateKeys() (priv, pub [32]byte) {
	io.ReadFull(rand.Reader, priv[:])
	curve25519.ScalarBaseMult(&pub, &priv)
	return
}

func deriveKey(priv, peerPub [32]byte) []byte {
	secret, _ := curve25519.X25519(priv[:], peerPub[:])
	hash := sha256.Sum256(secret)
	return hash[:]
}

func signAuth(key []byte, data []byte) []byte {
	h := hmac.New(sha256.New, key)
	h.Write(data)
	return h.Sum(nil)
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

func sealPacket(dst []byte, aead cipher.AEAD, seq uint64, payload []byte) []byte {
	nonce := dst[1:13]
	binary.BigEndian.PutUint32(nonce[:4], 0xDEADBEEF)
	binary.BigEndian.PutUint64(nonce[4:], seq)
	return aead.Seal(dst[:13], nonce, payload, nil)
}

func openPacket(raw []byte, aead cipher.AEAD) ([]byte, uint64, error) {
	if len(raw) < OVERHEAD {
		return nil, 0, fmt.Errorf("short")
	}
	nonce := raw[1:13]
	seq := binary.BigEndian.Uint64(nonce[4:])
	out, err := aead.Open(nil, nonce, raw[13:], nil)
	return out, seq, err
}

// --- Network Management ---

func setupNetworking(name string, peerIP string, isServer bool) {
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

	if isServer {
		runCmd("ip", "addr", "replace", "10.0.0.1/24", "dev", name)
		runCmd("sysctl", "-w", "net.ipv4.ip_forward=1")
		runCmd("iptables", "-t", "nat", "-A", "POSTROUTING", "-o", dev, "-m", "comment", "--comment", "WOLFVPN", "-j", "MASQUERADE")
		runCmd("iptables", "-A", "FORWARD", "-i", name, "-j", "ACCEPT")
	} else if peerIP != "" {
		runCmd("ip", "route", "add", peerIP, "via", gw, "dev", dev)
		runCmd("iptables", "-N", "WOLF_VPN")
		runCmd("iptables", "-I", "OUTPUT", "1", "-j", "WOLF_VPN")
		runCmd("iptables", "-A", "WOLF_VPN", "-o", "lo", "-j", "ACCEPT")
		runCmd("iptables", "-A", "WOLF_VPN", "-d", peerIP, "-p", "udp", "-j", "ACCEPT")
		runCmd("iptables", "-A", "WOLF_VPN", "-o", name, "-j", "ACCEPT")
		runCmd("iptables", "-A", "WOLF_VPN", "-j", "DROP")
		runCmd("ip", "route", "add", "0.0.0.0/1", "dev", name)
		runCmd("ip", "route", "add", "128.0.0.0/1", "dev", name)
	}
}

func cleanup(isServer bool) {
	if isServer {
		runCmd("iptables", "-t", "nat", "-D", "POSTROUTING", "-m", "comment", "--comment", "WOLFVPN", "-j", "MASQUERADE")
	} else {
		runCmd("iptables", "-D", "OUTPUT", "-j", "WOLF_VPN")
		runCmd("iptables", "-F", "WOLF_VPN")
		runCmd("iptables", "-X", "WOLF_VPN")
	}
	runCmd("sysctl", "-w", "net.ipv4.ip_forward="+origForwarding)
	os.Exit(0)
}

// --- Main ---

func main() {
	lPort := flag.Int("l", 9000, "Local Port")
	apiPort := flag.Int("api", 8080, "Web API Port")
	tAddrStr := flag.String("t", "", "Target Host/IP")
	pass := flag.String("p", "WolfPass", "Secret")
	isServer := flag.Bool("server", false, "Server Mode")
	flag.Parse()

	runtime.GOMAXPROCS(runtime.NumCPU())
	tun, _ := water.New(water.Config{DeviceType: water.TUN})

	var currentTarget *net.UDPAddr
	var targetHost string
	if *tAddrStr != "" {
		currentTarget, _ = net.ResolveUDPAddr("udp", *tAddrStr)
		if currentTarget != nil {
			targetHost = currentTarget.IP.String()
		}
	}

	setupNetworking(tun.Name(), targetHost, *isServer)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGINT, syscall.SIGTERM)
	go func() { <-sig; cleanup(*isServer) }()

	lAddr, _ := net.ResolveUDPAddr("udp", fmt.Sprintf(":%d", *lPort))
	conn, _ = net.ListenUDP("udp", lAddr)

	myPriv, myPub := generateKeys()

	if *isServer {
		// --- The Reaper ---
		go func() {
			for range time.Tick(60 * time.Second) {
				now := time.Now().Unix()
				mgr.ByIdentity.Range(func(key, value interface{}) bool {
					s := value.(*UserSession)
					if now-atomic.LoadInt64(&s.LastSeen) > SESSION_TTL {
						fmt.Printf("[!] Reaper: Evicting %s (%s)\n", key.(string)[:8], s.InternalIP)
						mgr.ByIdentity.Delete(key)
						mgr.ByIP.Delete(s.InternalIP)
						mgr.ByAddr.Delete(s.Addr.String())
					}
					return true
				})
			}
		}()

		// Dashboard
		http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
			w.Header().Set("Content-Type", "text/html")
			fmt.Fprintf(w, "<body style='background:#0f172a;color:white;font-family:sans-serif;padding:40px;'><h1>Wolf VPN</h1>")
			mgr.ByIdentity.Range(func(k, v interface{}) bool {
				s := v.(*UserSession)
				fmt.Fprintf(w, "<p><b>ID:</b> %s | <b>IP:</b> %s | <b>Last Seen:</b> %ds ago</p>", k.(string)[:8], s.InternalIP, time.Now().Unix()-atomic.LoadInt64(&s.LastSeen))
				return true
			})
			fmt.Fprintf(w, "</body><script>setTimeout(()=>location.reload(),5000)</script>")
		})
		go http.ListenAndServe(fmt.Sprintf(":%d", *apiPort), nil)
	}

	// Worker Loop
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for {
				buf := bufferPool.Get().([]byte)
				n, rem, err := conn.ReadFromUDP(buf)
				if err != nil {
					continue
				}

				switch buf[0] {
				case OP_DATA:
					var aead cipher.AEAD
					var s *UserSession
					if val, ok := mgr.ByAddr.Load(rem.String()); ok {
						s = val.(*UserSession)
						aead = s.AEAD
					} else if !*isServer {
						if val := clientAEAD.Load(); val != nil {
							aead = val.(cipher.AEAD)
						}
					}
					if aead != nil {
						plain, seq, err := openPacket(buf[:n], aead)
						if err == nil && (!*isServer || s.VerifySeq(seq)) {
							tun.Write(plain)
							if *isServer {
								atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
							} else {
								atomic.StoreInt64(&lastActivity, time.Now().Unix())
							}
						}
					}

				case OP_AUTH:
					if *isServer && n >= 65 {
						clientPubRaw := buf[1:33]
						if hmac.Equal(buf[33:65], signAuth([]byte(*pass), clientPubRaw)) {
							id := hex.EncodeToString(clientPubRaw)
							var s *UserSession
							if val, ok := mgr.ByIdentity.Load(id); ok {
								s = val.(*UserSession)
								s.Addr = rem
							} else {
								// --- Smart IP Allocator ---
								var assignedIP string
								for i := 2; i < 255; i++ {
									candidate := fmt.Sprintf("10.0.0.%d", i)
									if _, occupied := mgr.ByIP.Load(candidate); !occupied {
										assignedIP = candidate
										break
									}
								}
								if assignedIP != "" {
									var cp [32]byte
									copy(cp[:], clientPubRaw)
									aead, _ := chacha20poly1305.New(deriveKey(myPriv, cp))
									s = &UserSession{Addr: rem, InternalIP: assignedIP, AEAD: aead}
									mgr.ByIdentity.Store(id, s)
									mgr.ByIP.Store(assignedIP, s)
								}
							}
							if s != nil {
								mgr.ByAddr.Store(rem.String(), s)
								atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
								resp := append([]byte{OP_AUTH}, myPub[:]...)
								conn.WriteToUDP(append(resp, []byte(s.InternalIP)...), rem)
							}
						}
					} else if !*isServer {
						var sp [32]byte
						copy(sp[:], buf[1:33])
						clientAEAD.Store(func() cipher.AEAD { a, _ := chacha20poly1305.New(deriveKey(myPriv, sp)); return a }())
						assignedIP := string(buf[33:n])
						runCmd("ip", "addr", "flush", "dev", tun.Name())
						runCmd("ip", "addr", "add", assignedIP+"/24", "dev", tun.Name())
						atomic.StoreInt64(&lastActivity, time.Now().Unix())
					}

				case OP_KEEPALIVE:
					if val, ok := mgr.ByAddr.Load(rem.String()); ok {
						atomic.StoreInt64(&val.(*UserSession).LastSeen, time.Now().Unix())
					}
				}
				bufferPool.Put(buf)
			}
		}()
	}

	// Client Loop (DDNS + Handshake)
	go func() {
		for range time.Tick(10 * time.Second) {
			if !*isServer && *tAddrStr != "" {
				if addr, err := net.ResolveUDPAddr("udp", *tAddrStr); err == nil {
					currentTarget = addr
				}
				if currentTarget == nil {
					continue
				}
				if time.Now().Unix()-atomic.LoadInt64(&lastActivity) > 20 {
					req := append([]byte{OP_AUTH}, myPub[:]...)
					conn.WriteToUDP(append(req, signAuth([]byte(*pass), myPub[:])...), currentTarget)
				} else {
					conn.WriteToUDP([]byte{OP_KEEPALIVE}, currentTarget)
				}
			}
		}
	}()

	// Outbound Tunnel
	for {
		pkt := make([]byte, 2048)
		n, _ := tun.Read(pkt)
		tx := make([]byte, 2048)
		tx[0] = OP_DATA
		if *isServer && n >= 20 {
			destIP := net.IP(pkt[16:20]).String()
			if val, ok := mgr.ByIP.Load(destIP); ok {
				s := val.(*UserSession)
				conn.WriteToUDP(sealPacket(tx, s.AEAD, atomic.AddUint64(&s.SeqOut, 1), pkt[:n]), s.Addr)
			}
		} else if !*isServer {
			if val := clientAEAD.Load(); val != nil && currentTarget != nil {
				conn.WriteToUDP(sealPacket(tx, val.(cipher.AEAD), atomic.AddUint64(&clientSeq, 1), pkt[:n]), currentTarget)
			}
		}
	}
}
