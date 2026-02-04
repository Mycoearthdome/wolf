package main

import (
	"crypto/cipher"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
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
	BytesIn    uint64
	BytesOut   uint64
}

type SessionManager struct {
	ByIdentity sync.Map
	ByAddr     sync.Map
	ByIP       sync.Map
}

type PeerStat struct {
	ID     string `json:"id"`
	IP     string `json:"ip"`
	TX     string `json:"tx"`
	RX     string `json:"rx"`
	LT     int64  `json:"lt"`
	Status string `json:"status"`
}

type GeoData struct {
	City    string  `json:"city"`
	Country string  `json:"country"`
	Flag    string  `json:"flag"`
	Lat     float64 `json:"lat"`
	Lon     float64 `json:"lon"`
}

var (
	startTime      = time.Now()
	mgr            = &SessionManager{}
	conn           *net.UDPConn
	origForwarding string
	clientAEAD     atomic.Value
	clientSeq      uint64
	lastActivity   int64
	totalBytes     uint64
	historyMu      sync.RWMutex
	trafficHistory = make([]uint64, 60)
	bufferPool     = sync.Pool{New: func() interface{} { return make([]byte, 2048) }}
	banMap         sync.Map // IP string -> int64 (expiry timestamp)
	geoCache       sync.Map // IP string -> GeoData
	globalLockdown uint32   // 0 = normal, 1 = drop all
	sysLog         []string
	logMu          sync.Mutex
)

// --- Helpers ---

func runCmd(c string, args ...string) { _ = exec.Command(c, args...).Run() }

func formatBytes(b uint64) string {
	const unit = 1024
	if b < unit {
		return fmt.Sprintf("%d B", b)
	}
	div, exp := uint64(unit), 0
	for n := b / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %cB", float64(b)/float64(div), "KMGTPE"[exp])
}

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

func setupNetworking(name string, peerStr string, isServer bool) {
	outFwd, _ := exec.Command("sysctl", "-n", "net.ipv4.ip_forward").Output()
	origForwarding = strings.TrimSpace(string(outFwd))

	// Find the physical interface and gateway
	outRoute, _ := exec.Command("ip", "route", "show", "default").Output()
	fields := strings.Fields(string(outRoute))
	var dev, gateway string
	for i, f := range fields {
		if f == "dev" {
			dev = fields[i+1]
		}
		if f == "via" {
			gateway = fields[i+1]
		}
	}

	runCmd("ip", "link", "set", "dev", name, "up", "mtu", fmt.Sprintf("%d", TUN_MTU))

	if isServer {
		fmt.Println("[SYS] Mode: SERVER | Interface:", name)
		runCmd("ip", "addr", "replace", "10.0.0.1/24", "dev", name)
		runCmd("sysctl", "-w", "net.ipv4.ip_forward=1")
		if dev != "" {
			runCmd("iptables", "-t", "nat", "-A", "POSTROUTING", "-o", dev, "-m", "comment", "--comment", "WOLFVPN", "-j", "MASQUERADE")
			runCmd("iptables", "-A", "FORWARD", "-i", name, "-j", "ACCEPT")
		}
	} else {
		fmt.Println("[SYS] Mode: CLIENT | Target:", peerStr)
		// Extract server IP to prevent routing loops
		serverIP := strings.Split(peerStr, ":")[0]
		if serverIP != "" && gateway != "" {
			// Pin the server's IP to the physical gateway
			runCmd("ip", "route", "add", serverIP, "via", gateway)
		}
	}
}

func cleanup(isServer bool) {
	fmt.Println("\n[SYS] Cleaning up...")
	if isServer {
		runCmd("iptables", "-t", "nat", "-D", "POSTROUTING", "-m", "comment", "--comment", "WOLFVPN", "-j", "MASQUERADE")
	}
	runCmd("sysctl", "-w", "net.ipv4.ip_forward="+origForwarding)
	os.Exit(0)
}

func main() {
	lPort := flag.Int("l", 9000, "Local Port")
	apiPort := flag.Int("api", 8080, "Web API Port")
	tAddrStr := flag.String("t", "", "Target Host/IP")
	pass := flag.String("p", "BatMan", "Secret")
	isServer := flag.Bool("server", false, "Server Mode")
	flag.Parse()

	runtime.GOMAXPROCS(runtime.NumCPU())
	tun, err := water.New(water.Config{DeviceType: water.TUN})
	if err != nil {
		fmt.Println("Err TUN:", err)
		return
	}

	var currentTarget *net.UDPAddr
	if *tAddrStr != "" {
		if !strings.Contains(*tAddrStr, ":") {
			*tAddrStr += ":9000"
		}
		currentTarget, _ = net.ResolveUDPAddr("udp", *tAddrStr)
	}

	setupNetworking(tun.Name(), *tAddrStr, *isServer)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGINT, syscall.SIGTERM)
	go func() { <-sig; cleanup(*isServer); os.Exit(0) }()

	lAddr, _ := net.ResolveUDPAddr("udp", fmt.Sprintf(":%d", *lPort))
	conn, _ = net.ListenUDP("udp", lAddr)
	myPriv, myPub := generateKeys()

	// --- 1. Stats & Web UI (Server Only) ---
	if *isServer {
		historyMu.Lock()
		trafficHistory = make([]uint64, 60)
		historyMu.Unlock()

		// Stats Engine
		go func() {
			var lastTotal uint64
			ticker := time.NewTicker(1 * time.Second)
			for range ticker.C {
				currentTotal := atomic.LoadUint64(&totalBytes)
				delta := uint64(0)
				if currentTotal >= lastTotal {
					delta = currentTotal - lastTotal
				}
				lastTotal = currentTotal

				historyMu.Lock()
				trafficHistory = append(trafficHistory, delta)
				if len(trafficHistory) > 60 {
					trafficHistory = trafficHistory[len(trafficHistory)-60:]
				}
				historyMu.Unlock()
			}
		}()

		// Session Reaper
		go func() {
			for range time.Tick(30 * time.Second) {
				now := time.Now().Unix()
				mgr.ByIdentity.Range(func(k, v interface{}) bool {
					s := v.(*UserSession)
					if now-atomic.LoadInt64(&s.LastSeen) > 120 {
						mgr.ByIdentity.Delete(k)
						mgr.ByAddr.Delete(s.Addr.String())
						mgr.ByIP.Delete(s.InternalIP)
					}
					return true
				})
			}
		}()

		// API Endpoint
		http.HandleFunc("/api/stats", func(w http.ResponseWriter, r *http.Request) {
			peers := []interface{}{}
			now := time.Now().Unix()
			mgr.ByIdentity.Range(func(k, v interface{}) bool {
				s := v.(*UserSession)
				ls := atomic.LoadInt64(&s.LastSeen)
				diff := now - ls
				status := "STABLE"
				if diff > 30 {
					status = "GHOST"
				} else if diff > 10 {
					status = "LAGGING"
				}

				extIP := strings.Split(s.Addr.String(), ":")[0]
				city, flag, lat, lon := "Unknown", "🌐", 0.0, 0.0
				if geo, ok := geoCache.Load(extIP); ok {
					g := geo.(GeoData)
					city, flag, lat, lon = g.City, g.Flag, g.Lat, g.Lon
				}

				peers = append(peers, map[string]interface{}{
					"id":         k.(string),     // FULL ID for the backend "kick/ban" calls
					"display_id": k.(string)[:8], // SHORT ID for the UI table
					"ip":         s.InternalIP, "ext_ip": extIP,
					"lat": lat, "lon": lon, "city": city, "flag": flag,
					"tx":     formatBytes(atomic.LoadUint64(&s.BytesOut)),
					"rx":     formatBytes(atomic.LoadUint64(&s.BytesIn)),
					"status": status, "last_seen": diff,
				})
				return true
			})
			historyMu.RLock()
			histCopy := make([]uint64, len(trafficHistory))
			copy(histCopy, trafficHistory)
			historyMu.RUnlock()

			w.Header().Set("Content-Type", "application/json")
			json.NewEncoder(w).Encode(map[string]interface{}{
				"total": formatBytes(atomic.LoadUint64(&totalBytes)),
				"count": len(peers), "peers": peers, "hist": histCopy,
				"up":       time.Since(startTime).Truncate(time.Second).String(),
				"lockdown": atomic.LoadUint32(&globalLockdown),
			})
		})

		http.HandleFunc("/api/admin", adminHandler)
		http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
			w.Header().Set("Content-Type", "text/html")
			fmt.Fprint(w, dashboardHTML)
		})
		go http.ListenAndServe(fmt.Sprintf(":%d", *apiPort), nil)
	}

	// --- 2. UDP Receiver (Scaled Workers) ---
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for {
				buf := bufferPool.Get().([]byte)
				n, rem, err := conn.ReadFromUDP(buf)
				if err != nil {
					bufferPool.Put(buf)
					continue
				}
				if atomic.LoadUint32(&globalLockdown) == 1 {
					bufferPool.Put(buf)
					continue
				}

				if expiry, banned := banMap.Load(rem.IP.String()); banned {
					if time.Now().Unix() < expiry.(int64) {
						bufferPool.Put(buf)
						continue
					}
					banMap.Delete(rem.IP.String())
				}

				switch buf[0] {
				case OP_DATA:
					if val, ok := mgr.ByAddr.Load(rem.String()); ok {
						s := val.(*UserSession)
						atomic.AddUint64(&s.BytesIn, uint64(n))
						atomic.AddUint64(&totalBytes, uint64(n))
						atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
						plain, seq, err := openPacket(buf[:n], s.AEAD)
						if err == nil && s.VerifySeq(seq) {
							tun.Write(plain)
						}
					} else if !*isServer {
						if val := clientAEAD.Load(); val != nil {
							atomic.AddUint64(&totalBytes, uint64(n))
							atomic.StoreInt64(&lastActivity, time.Now().Unix())
							if plain, _, err := openPacket(buf[:n], val.(cipher.AEAD)); err == nil {
								tun.Write(plain)
							}
						}
					}
				case OP_AUTH:
					if *isServer && n >= 65 {
						clientPubRaw := buf[1:33]
						if hmac.Equal(buf[33:65], signAuth([]byte(*pass), clientPubRaw)) {
							id := hex.EncodeToString(clientPubRaw)
							if val, ok := mgr.ByIdentity.Load(id); ok {
								s := val.(*UserSession)
								if s.Addr.String() != rem.String() {
									mgr.ByAddr.Delete(s.Addr.String())
									s.Addr = rem
									pushLog("NODE_MIGRATE: " + s.InternalIP + " moved to " + rem.String())
								}
								mgr.ByAddr.Store(rem.String(), s)
								atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
								resp := append([]byte{OP_AUTH}, myPub[:]...)
								conn.WriteToUDP(append(resp, []byte(s.InternalIP)...), rem)
								bufferPool.Put(buf)
								continue
							}
							assignedIP := ""
							for i := 2; i < 255; i++ {
								ip := fmt.Sprintf("10.0.0.%d", i)
								if _, occupied := mgr.ByIP.Load(ip); !occupied {
									assignedIP = ip
									break
								}
							}
							if assignedIP != "" {
								var cp [32]byte
								copy(cp[:], clientPubRaw)
								aead, _ := chacha20poly1305.New(deriveKey(myPriv, cp))
								s := &UserSession{Addr: rem, InternalIP: assignedIP, AEAD: aead, LastSeen: time.Now().Unix()}
								mgr.ByIdentity.Store(id, s)
								mgr.ByIP.Store(assignedIP, s)
								mgr.ByAddr.Store(rem.String(), s)

								// CRITICAL: Log new joins to the system log
								pushLog("NODE_JOIN: " + assignedIP + " from " + rem.IP.String() + " [" + id[:8] + "]")

								go updateGeoInfo(rem.IP.String())
								resp := append([]byte{OP_AUTH}, myPub[:]...)
								conn.WriteToUDP(append(resp, []byte(s.InternalIP)...), rem)
							}
						}
					} else if !*isServer && n >= 33 {
						var sp [32]byte
						copy(sp[:], buf[1:33])
						aead, _ := chacha20poly1305.New(deriveKey(myPriv, sp))
						clientAEAD.Store(aead)
						assignedIP := string(buf[33:n])
						runCmd("ip", "addr", "replace", assignedIP+"/24", "dev", tun.Name())
						out, _ := exec.Command("ip", "route", "show", "default").Output()
						fields := strings.Fields(string(out))
						var gw string
						for i, f := range fields {
							if f == "via" {
								gw = fields[i+1]
								break
							}
						}
						if currentTarget != nil && gw != "" {
							runCmd("ip", "route", "add", currentTarget.IP.String(), "via", gw)
						}
						runCmd("ip", "route", "add", "0.0.0.0/1", "dev", tun.Name())
						runCmd("ip", "route", "add", "128.0.0.0/1", "dev", tun.Name())
						atomic.StoreInt64(&lastActivity, time.Now().Unix())
					}
				}
				bufferPool.Put(buf)
			}
		}()
	}

	// --- 3. Client Handshake / Keepalive (One instance only) ---
	if !*isServer {
		go func() {
			for range time.Tick(5 * time.Second) {
				if currentTarget != nil {
					if time.Now().Unix()-atomic.LoadInt64(&lastActivity) > 15 {
						req := append([]byte{OP_AUTH}, myPub[:]...)
						conn.WriteToUDP(append(req, signAuth([]byte(*pass), myPub[:])...), currentTarget)
					} else {
						conn.WriteToUDP([]byte{OP_KEEPALIVE}, currentTarget)
					}
				}
			}
		}()
	}

	// --- 4. TUN Reader (Main Loop) ---
	for {
		pkt := make([]byte, 2048)
		n, err := tun.Read(pkt)
		if err != nil {
			continue
		}

		if *isServer && n >= 20 {
			destIP := net.IP(pkt[16:20]).String()
			if val, ok := mgr.ByIP.Load(destIP); ok {
				s := val.(*UserSession)
				tx := make([]byte, n+OVERHEAD)
				tx[0] = OP_DATA
				enc := sealPacket(tx, s.AEAD, atomic.AddUint64(&s.SeqOut, 1), pkt[:n])
				conn.WriteToUDP(enc, s.Addr)
				atomic.AddUint64(&s.BytesOut, uint64(len(enc)))
				atomic.AddUint64(&totalBytes, uint64(len(enc)))
			}
		} else if !*isServer {
			if val := clientAEAD.Load(); val != nil && currentTarget != nil {
				tx := make([]byte, n+OVERHEAD)
				tx[0] = OP_DATA
				enc := sealPacket(tx, val.(cipher.AEAD), atomic.AddUint64(&clientSeq, 1), pkt[:n])
				conn.WriteToUDP(enc, currentTarget)
				atomic.AddUint64(&totalBytes, uint64(len(enc)))
			}
		}
	}
}

// Helper to push to history
func pushLog(msg string) {
	logMu.Lock()
	defer logMu.Unlock()
	sysLog = append(sysLog, fmt.Sprintf("[%s] %s", time.Now().Format("15:04:05"), msg))
	if len(sysLog) > 500 {
		sysLog = sysLog[1:]
	} // Keep last 500 lines
}

func adminHandler(w http.ResponseWriter, r *http.Request) {
	action := r.URL.Query().Get("action")
	target := r.URL.Query().Get("target")

	switch action {
	case "get_logs":
		logMu.Lock()
		data := strings.Join(sysLog, "\n")
		logMu.Unlock()
		w.Header().Set("Content-Type", "text/plain")
		fmt.Fprint(w, data)
		return

	case "lockdown":
		for {
			old := atomic.LoadUint32(&globalLockdown)
			newVal := uint32(0)
			if old == 0 {
				newVal = 1
			}
			if atomic.CompareAndSwapUint32(&globalLockdown, old, newVal) {
				stateStr := "ENABLED"
				if newVal == 0 {
					stateStr = "DISABLED"
				}
				pushLog("SECURITY_ALERT: Global Lockdown " + stateStr)
				break
			}
		}

	case "kick":
		if val, ok := mgr.ByIdentity.Load(target); ok {
			s := val.(*UserSession)
			mgr.ByIdentity.Delete(target)
			mgr.ByAddr.Delete(s.Addr.String())
			mgr.ByIP.Delete(s.InternalIP)
			pushLog("TERMINATE_PROTOCOL: Node [" + target[:8] + "] disconnected by SYSOP")
		}

	case "ban":
		if target != "" {
			// Ban for 1 hour
			expiry := time.Now().Unix() + 3600
			banMap.Store(target, expiry)
			pushLog("BAN_PROTOCOL: External IP [" + target + "] blacklisted for 3600s")

			// Purge any active session belonging to this IP
			mgr.ByIdentity.Range(func(k, v interface{}) bool {
				s := v.(*UserSession)
				if strings.Split(s.Addr.String(), ":")[0] == target {
					mgr.ByIdentity.Delete(k)
					mgr.ByAddr.Delete(s.Addr.String())
					mgr.ByIP.Delete(s.InternalIP)
				}
				return true
			})
		}

	case "reset_stats":
		atomic.StoreUint64(&totalBytes, 0)
		historyMu.Lock()
		for i := range trafficHistory {
			trafficHistory[i] = 0
		}
		historyMu.Unlock()
		pushLog("SYSTEM_MAINTENANCE: Traffic statistics purged")
	}

	w.WriteHeader(http.StatusOK)
}

func updateGeoInfo(ip string) {
	if _, exists := geoCache.Load(ip); exists {
		return
	}

	// Don't lookup local addresses
	if ip == "127.0.0.1" || strings.HasPrefix(ip, "192.168.") || strings.HasPrefix(ip, "10.") {
		geoCache.Store(ip, GeoData{City: "Internal", Country: "LAN", Flag: "🏠", Lat: 0, Lon: 0})
		return
	}

	client := http.Client{Timeout: 3 * time.Second}
	url := fmt.Sprintf("http://ip-api.com/json/%s?fields=status,countryCode,city,lat,lon", ip)
	resp, err := client.Get(url)
	if err != nil {
		return
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		return
	}

	var res struct {
		Status  string  `json:"status"`
		Country string  `json:"countryCode"`
		City    string  `json:"city"`
		Lat     float64 `json:"lat"`
		Lon     float64 `json:"lon"`
	}

	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil || res.Status != "success" {
		return
	}

	// --- SAFETY CHECK FOR FLAGS ---
	flagEmoji := "🌐"
	if len(res.Country) == 2 {
		// Convert ISO 3166-1 alpha-2 to Regional Indicator Symbols
		r1 := rune(res.Country[0]) + 127397
		r2 := rune(res.Country[1]) + 127397
		flagEmoji = string(r1) + string(r2)
	}

	geoCache.Store(ip, GeoData{
		City:    res.City,
		Country: res.Country,
		Flag:    flagEmoji,
		Lat:     res.Lat,
		Lon:     res.Lon,
	})
}

const dashboardHTML = `
<!DOCTYPE html>
<html class="dark">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <script src="https://cdn.tailwindcss.com"></script>
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <script src="https://unpkg.com/topojson@3"></script>
    <style>
        @import url('https://fonts.googleapis.com/css2?family=Orbitron:wght@400;700&family=JetBrains+Mono&display=swap');
        :root { --cyan: #00f2ff; --pink: #ff0055; --bg: #020408; }
        body { background: var(--bg); color: #94a3b8; font-family: 'JetBrains Mono', monospace; overflow: hidden; margin: 0; height: 100vh; }
        #world-map { position: fixed; inset: 0; opacity: 0.15; z-index: 0; }
        .panel { background: rgba(10, 15, 28, 0.9); backdrop-filter: blur(10px); border: 1px solid rgba(0, 242, 255, 0.1); }
        .glow { text-shadow: 0 0 10px var(--cyan); color: white; font-family: 'Orbitron'; }
        .lockdown-ui { border-color: var(--pink) !important; background: rgba(30, 0, 0, 0.9) !important; }
        .btn { font-size: 10px; padding: 5px 15px; border: 1px solid var(--cyan); color: var(--cyan); cursor: pointer; text-transform: uppercase; clip-path: polygon(10% 0, 100% 0, 100% 70%, 90% 100%, 0 100%, 0 30%); transition: all 0.2s; }
        .btn:hover { background: var(--cyan); color: #000; box-shadow: 0 0 15px var(--cyan); }
        .btn-red { border-color: var(--pink); color: var(--pink); }
        .btn-red:hover { background: var(--pink); color: #fff; box-shadow: 0 0 15px var(--pink); }
        
        /* Modal Styles */
        .modal-content { background: #05070a; border: 1px solid var(--cyan); box-shadow: 0 0 50px rgba(0, 242, 255, 0.1); }
        textarea::-webkit-scrollbar { width: 6px; }
        textarea::-webkit-scrollbar-thumb { background: #1e293b; border-radius: 10px; }
    </style>
</head>
<body>
    <div id="world-map"></div>

    <div id="log-modal" class="hidden fixed inset-0 z-50 flex items-center justify-center bg-black/80 backdrop-blur-md p-6">
        <div class="modal-content w-full max-w-4xl h-[80vh] flex flex-col p-6 overflow-hidden">
            <div class="flex justify-between items-center mb-4 border-b border-cyan-500/20 pb-4">
                <h2 class="glow text-lg">SYSTEM_LOG_EXPLORER</h2>
                <button onclick="closeLogExplorer()" class="text-pink-500 hover:text-white font-bold text-xs">[ CLOSE_ESCAPE ]</button>
            </div>
            <textarea id="log-content" readonly class="flex-1 bg-black/40 p-4 text-cyan-400 font-mono text-[10px] resize-none outline-none border border-white/5" placeholder="Awaiting data stream..."></textarea>
            <div class="mt-4 flex justify-between items-center">
                <button onclick="copyLogs()" class="btn">Copy_To_Clipboard</button>
                <span class="text-[8px] text-slate-600 italic">// END_OF_VOLATILE_BUFFER</span>
            </div>
        </div>
    </div>

    <div class="relative z-10 h-screen flex flex-col p-6">
        <div id="header-panel" class="flex justify-between items-center mb-6 p-4 panel border-l-4 border-l-[#00f2ff]">
            <div>
                <h1 class="text-xl font-black italic glow">WOLF_SYSOP</h1>
                <div class="flex gap-4 mt-1 text-[9px]">
                    <span class="text-cyan-400">UP: <span id="stat-up">--</span></span>
                    <span class="text-slate-500">TOTAL_TRAFFIC: <span id="stat-total">--</span></span>
                </div>
            </div>
            <div class="flex gap-3">
                <button onclick="openLogExplorer()" class="btn">Explore_Logs</button>
                <button id="lockdown-btn" onclick="adminAction('lockdown')" class="btn btn-red">Enable Lockdown</button>
            </div>
        </div>

        <div class="grid grid-cols-12 gap-6 flex-1 overflow-hidden">
            <div class="col-span-8 flex flex-col gap-6 overflow-hidden">
                <div class="panel flex-1 overflow-hidden flex flex-col">
                    <div class="p-3 border-b border-white/5 bg-white/5 text-[10px] font-bold text-cyan-400 flex justify-between">
                        <span>NODE_REGISTRY</span>
                        <span id="stat-count">0 ACTIVE</span>
                    </div>
                    <div class="overflow-y-auto flex-1">
                        <table class="w-full text-left text-[11px]">
                            <thead class="sticky top-0 bg-[#0a0f1c] text-slate-500 uppercase text-[8px]">
                                <tr><th class="p-4">Identity</th><th class="p-4">Location</th><th class="p-4">Status</th><th class="p-4 text-right">Control</th></tr>
                            </thead>
                            <tbody id="peer-list"></tbody>
                        </table>
                    </div>
                </div>
            </div>

            <div class="col-span-4 flex flex-col gap-6 overflow-hidden">
                <div class="panel p-4 h-1/3">
                    <canvas id="trafficChart"></canvas>
                </div>
                <div class="panel p-4 flex-1 overflow-y-auto font-mono text-[9px] text-cyan-800" id="log-container">
                    <div>[SYSTEM] INITIALIZING_DASHBOARD...</div>
                </div>
            </div>
        </div>
    </div>

    <script>
        const svg = d3.select("#world-map").append("svg").attr("width", "100%").attr("height", "100%");
        const mapGroup = svg.append("g");
        const projection = d3.geoMercator().scale(150).translate([window.innerWidth/2, window.innerHeight/1.5]);

        d3.json("https://cdn.jsdelivr.net/npm/world-atlas@2/countries-110m.json").then(data => {
            mapGroup.selectAll("path").data(topojson.feature(data, data.objects.countries).features)
                .enter().append("path").attr("d", d3.geoPath().projection(projection))
                .attr("fill", "#0f172a").attr("stroke", "#1e293b");
        });

        async function update() {
            try {
                const r = await fetch("/api/stats");
                const d = await r.json();
                
                document.getElementById("stat-total").innerText = d.total;
                document.getElementById("stat-count").innerText = d.count + " ACTIVE NODES";
                document.getElementById("stat-up").innerText = d.up;

                const isLocked = d.lockdown === 1;
                document.getElementById("header-panel").classList.toggle('lockdown-ui', isLocked);
                document.getElementById("lockdown-btn").innerText = isLocked ? "Disable Lockdown" : "Enable Lockdown";

                const tbody = document.getElementById("peer-list");
                tbody.innerHTML = "";
                (d.peers || []).forEach(p => {
                    const row = document.createElement("tr");
                    row.className = "border-b border-white/5 hover:bg-white/5 transition-colors";
                    row.innerHTML = '<td class="p-4"><div class="text-white font-bold">' + p.display_id + '</div><div class="text-[9px] text-cyan-600">' + p.ip + '</div></td>' +
                        '<td class="p-4"><span class="text-lg">' + (p.flag || '🌐') + '</span> <span class="ml-2 text-slate-300">' + (p.city || 'Unknown') + '</span></td>' +
                        '<td class="p-4"><span class="px-2 py-0.5 rounded-full bg-cyan-500/10 text-cyan-400 text-[8px]">' + p.status + '</span></td>' +
                        '<td class="p-4 text-right flex gap-2 justify-end">' + 
                            '<button onclick="adminAction(\'kick\',\''+p.id+'\')" class="btn">Kick</button>' +
                            '<button onclick="adminAction(\'ban\',\''+p.ext_ip+'\')" class="btn btn-red">Ban</button>' +
                        '</td>';
                    tbody.appendChild(row);
                });

                if (d.hist) {
                    chart.data.datasets[0].data = d.hist;
                    chart.update('none');
                }

                const dots = mapGroup.selectAll(".dot").data(d.peers, p => p.id);
                dots.exit().remove();
                dots.enter().append("circle").attr("class", "dot").attr("r", 3).attr("fill", "#00f2ff")
                    .merge(dots)
                    .attr("cx", p => projection([p.lon, p.lat])[0])
                    .attr("cy", p => projection([p.lon, p.lat])[1]);

            } catch (e) { console.error("Poll error", e); }
        }

        async function adminAction(a, t = "") {
            await fetch("/api/admin?action=" + a + "&target=" + t);
            const log = document.getElementById('log-container');
            const div = document.createElement('div');
            div.innerText = "[" + new Date().toLocaleTimeString() + "] EXEC: " + a.toUpperCase() + " " + (t.length > 15 ? t.substring(0,8) : t);
            log.prepend(div);
            update();
        }

        async function openLogExplorer() {
            document.getElementById('log-modal').classList.remove('hidden');
            const r = await fetch("/api/admin?action=get_logs");
            const text = await r.text();
            document.getElementById('log-content').value = text || "[SYSTEM] NO_LOGS_RETRIEVED";
        }

        function closeLogExplorer() {
            document.getElementById('log-modal').classList.add('hidden');
        }

        function copyLogs() {
            const el = document.getElementById('log-content');
            el.select();
            document.execCommand('copy');
            alert("SYSOP_DATA_COPIED_TO_CLIPBOARD");
        }

        const chart = new Chart(document.getElementById('trafficChart'), {
            type: 'line',
            data: { labels: Array(60).fill(''), datasets: [{ borderColor: '#00f2ff', data: [], fill: true, backgroundColor: 'rgba(0, 242, 255, 0.05)', pointRadius: 0, tension: 0.4 }] },
            options: { responsive: true, maintainAspectRatio: false, plugins: { legend: false }, scales: { x: { display: false }, y: { display: false } } }
        });

        setInterval(update, 2000);
        update();
    </script>
</body>
</html>
`
