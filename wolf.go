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
	City    string `json:"city"`
	Country string `json:"countryCode"`
	Flag    string `json:"flag"` // emoji flag
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
	go func() { <-sig; cleanup(*isServer) }()

	lAddr, _ := net.ResolveUDPAddr("udp", fmt.Sprintf(":%d", *lPort))
	conn, _ = net.ListenUDP("udp", lAddr)
	myPriv, myPub := generateKeys()

	// --- 1. Stats & Web UI (Server Only) ---
	if *isServer {
		historyMu.Lock()
		trafficHistory = make([]uint64, 60)
		historyMu.Unlock()

		// Stats Engine: Run once per second to calculate deltas
		go func() {
			var lastTotal uint64
			ticker := time.NewTicker(1 * time.Second)
			defer ticker.Stop()

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

		// --- Session Reaper ---
		go func() {
			// Check every 30 seconds for ghost sessions
			for range time.Tick(30 * time.Second) {
				now := time.Now().Unix()
				reapedCount := 0

				mgr.ByIdentity.Range(func(k, v interface{}) bool {
					s := v.(*UserSession)
					// If no activity for 2 minutes, purge the session
					if now-atomic.LoadInt64(&s.LastSeen) > 120 {
						id := k.(string)
						mgr.ByIdentity.Delete(id)
						mgr.ByAddr.Delete(s.Addr.String())
						mgr.ByIP.Delete(s.InternalIP)
						reapedCount++
					}
					return true
				})

				if reapedCount > 0 {
					fmt.Printf("[SYS] REAPER: %d stale sessions purged from registry\n", reapedCount)
				}
			}
		}()

		// API Endpoint
		http.HandleFunc("/api/stats", func(w http.ResponseWriter, r *http.Request) {
			peers := []interface{}{}
			now := time.Now().Unix()

			mgr.ByIdentity.Range(func(k, v interface{}) bool {
				s := v.(*UserSession)
				ls := atomic.LoadInt64(&s.LastSeen)

				// Calculate health status based on LastSeen
				diff := now - ls
				status := "STABLE"
				if diff > 30 {
					status = "GHOST"
				} else if diff > 10 {
					status = "LAGGING"
				}

				extIP := strings.Split(s.Addr.String(), ":")[0]

				// Safety check for GeoCache to prevent nil pointer panics
				city, flag := "Unknown", "🌐"
				if geo, ok := geoCache.Load(extIP); ok {
					gData := geo.(GeoData)
					city = gData.City
					flag = gData.Flag
				}

				peers = append(peers, map[string]interface{}{
					"id":        k.(string)[:8],
					"ip":        s.InternalIP,
					"ext_ip":    extIP,
					"tx":        formatBytes(atomic.LoadUint64(&s.BytesOut)),
					"rx":        formatBytes(atomic.LoadUint64(&s.BytesIn)),
					"city":      city,
					"flag":      flag,
					"status":    status,
					"last_seen": diff, // Seconds since last contact
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
				"count": len(peers),
				"peers": peers,
				"hist":  histCopy,
				"up":    time.Since(startTime).Truncate(time.Second).String(),
			})
		})

		http.HandleFunc("/api/admin", adminHandler)
		http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
			w.Header().Set("Content-Type", "text/html")
			fmt.Fprint(w, dashboardHTML)
		})

		fmt.Printf("[WEB] Cyber-Dashboard active on :%d\n", *apiPort)
		go http.ListenAndServe(fmt.Sprintf(":%d", *apiPort), nil)
	}

	// --- 2. UDP Receiver ---
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for {
				buf := bufferPool.Get().([]byte)
				n, rem, err := conn.ReadFromUDP(buf)
				if err != nil {
					continue
				}

				// --- BAN CHECK ---
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
							plain, _, err := openPacket(buf[:n], val.(cipher.AEAD))
							if err == nil {
								tun.Write(plain)
							}
						}
					}
				case OP_AUTH:
					if *isServer && n >= 65 {
						clientPubRaw := buf[1:33]
						if hmac.Equal(buf[33:65], signAuth([]byte(*pass), clientPubRaw)) {
							id := hex.EncodeToString(clientPubRaw)

							// 1. RE-AUTH LOGIC: Check if we already know this user identity
							if val, ok := mgr.ByIdentity.Load(id); ok {
								s := val.(*UserSession)

								// If the physical UDP address changed (roaming), purge the old mapping
								if s.Addr.String() != rem.String() {
									mgr.ByAddr.Delete(s.Addr.String())
									s.Addr = rem
								}

								mgr.ByAddr.Store(rem.String(), s)
								atomic.StoreInt64(&s.LastSeen, time.Now().Unix())

								// Send ACK back to client with their existing Internal IP
								resp := append([]byte{OP_AUTH}, myPub[:]...)
								conn.WriteToUDP(append(resp, []byte(s.InternalIP)...), rem)
								continue
							}

							// 2. NEW SESSION ALLOCATION
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
								// Create security context
								aead, _ := chacha20poly1305.New(deriveKey(myPriv, cp))

								s := &UserSession{
									Addr:       rem,
									InternalIP: assignedIP,
									AEAD:       aead,
									LastSeen:   time.Now().Unix(),
								}

								// Store in all registries
								mgr.ByIdentity.Store(id, s)
								mgr.ByIP.Store(assignedIP, s)
								mgr.ByAddr.Store(rem.String(), s)

								go updateGeoInfo(rem.IP.String())

								// Send Handshake ACK
								resp := append([]byte{OP_AUTH}, myPub[:]...)
								conn.WriteToUDP(append(resp, []byte(s.InternalIP)...), rem)
								fmt.Printf("[AUTH] New Node: %s assigned to %s\n", id[:8], assignedIP)
							}
						}
					} else if !*isServer && n >= 33 {
						// --- CLIENT SIDE HANDSHAKE ACK ---
						// The server has verified our key and sent back its public key + our assigned IP
						var sp [32]byte
						copy(sp[:], buf[1:33])

						// Initialize local encryption
						aead, _ := chacha20poly1305.New(deriveKey(myPriv, sp))
						clientAEAD.Store(aead)

						assignedIP := string(buf[33:n])
						fmt.Printf("[SYS] Handshake Successful. Assigned IP: %s\n", assignedIP)

						// Apply the IP to the local TUN interface
						runCmd("ip", "addr", "replace", assignedIP+"/24", "dev", tun.Name())

						// Set up standard split-tunnel routing
						out, _ := exec.Command("ip", "route", "show", "default").Output()
						fields := strings.Fields(string(out))
						var gateway string
						for i, f := range fields {
							if f == "via" {
								gateway = fields[i+1]
								break
							}
						}

						if currentTarget != nil && gateway != "" {
							// Ensure traffic to the server itself goes over the physical line, not the tunnel
							runCmd("ip", "route", "add", currentTarget.IP.String(), "via", gateway)
						}

						// Route everything else through the tunnel
						runCmd("ip", "route", "add", "0.0.0.0/1", "dev", tun.Name())
						runCmd("ip", "route", "add", "128.0.0.0/1", "dev", tun.Name())

						atomic.StoreInt64(&lastActivity, time.Now().Unix())
					}
				}
				bufferPool.Put(buf)
			}
		}()
	}

	// --- 3. Handshake / Keepalive ---
	go func() {
		for range time.Tick(5 * time.Second) {
			if !*isServer && currentTarget != nil {
				if time.Now().Unix()-atomic.LoadInt64(&lastActivity) > 15 {
					req := append([]byte{OP_AUTH}, myPub[:]...)
					conn.WriteToUDP(append(req, signAuth([]byte(*pass), myPub[:])...), currentTarget)
				} else {
					conn.WriteToUDP([]byte{OP_KEEPALIVE}, currentTarget)
				}
			}
		}
	}()

	// --- 4. TUN Reader ---
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
				encrypted := sealPacket(tx, s.AEAD, atomic.AddUint64(&s.SeqOut, 1), pkt[:n])
				conn.WriteToUDP(encrypted, s.Addr)
				atomic.AddUint64(&s.BytesOut, uint64(len(encrypted)))
				atomic.AddUint64(&totalBytes, uint64(len(encrypted)))
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

const dashboardHTML = `
<!DOCTYPE html>
<html class="dark">
<head>
    <meta charset="UTF-8">
    <script src="https://cdn.tailwindcss.com"></script>
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <style>
        @import url('https://fonts.googleapis.com/css2?family=Orbitron:wght@400;700&family=JetBrains+Mono&display=swap');
        
        :root {
            --neon-cyan: #00f2ff;
            --neon-pink: #ff0055;
            --void-bg: #020408;
        }

        body { 
            background: radial-gradient(circle at center, #0a0f1d 0%, var(--void-bg) 100%);
            color: #94a3b8; 
            font-family: 'JetBrains Mono', monospace; 
            overflow-x: hidden;
        }

        .cyber-panel { 
            background: rgba(15, 23, 42, 0.7); 
            backdrop-filter: blur(12px);
            border: 1px solid rgba(0, 242, 255, 0.2);
            box-shadow: 0 0 15px rgba(0, 0, 0, 0.5);
            position: relative;
        }

        .cyber-panel::before {
            content: "";
            position: absolute;
            top: 0; left: 0; width: 100%; height: 100%;
            background: linear-gradient(rgba(18, 16, 16, 0) 50%, rgba(0, 0, 0, 0.1) 50%), 
                        linear-gradient(90deg, rgba(255, 0, 0, 0.03), rgba(0, 255, 0, 0.01), rgba(0, 0, 255, 0.03));
            background-size: 100% 2px, 3px 100%;
            pointer-events: none;
        }

        h1, h2 { font-family: 'Orbitron', sans-serif; text-transform: uppercase; letter-spacing: 2px; }
        
        .glow-text { text-shadow: 0 0 10px var(--neon-cyan); color: white; }
        .glow-pink { text-shadow: 0 0 10px var(--neon-pink); color: var(--neon-pink); }

        .btn-cyber {
            font-size: 10px;
            font-weight: bold;
            padding: 5px 15px;
            border: 1px solid;
            transition: all 0.3s ease;
            clip-path: polygon(10% 0, 100% 0, 100% 70%, 90% 100%, 0 100%, 0 30%);
        }

        .btn-cyan { border-color: var(--neon-cyan); color: var(--neon-cyan); }
        .btn-cyan:hover { background: var(--neon-cyan); color: black; box-shadow: 0 0 20px var(--neon-cyan); }
        
        .btn-ban { border-color: var(--neon-pink); color: var(--neon-pink); }
        .btn-ban:hover { background: var(--neon-pink); color: white; box-shadow: 0 0 20px var(--neon-pink); }

        .scanline {
            width: 100%; height: 2px; background: rgba(0, 242, 255, 0.1);
            position: fixed; top: 0; z-index: 999; pointer-events: none;
            animation: scan 8s linear infinite;
        }

        @keyframes scan { from { top: 0; } to { top: 100vh; } }
    </style>
</head>
<body class="p-6">
    <div class="scanline"></div>
    <div class="max-w-7xl mx-auto">
        <div class="flex justify-between items-center mb-8 p-6 cyber-panel border-l-4 border-l-[#00f2ff]">
            <div>
                <h1 class="text-3xl font-black italic glow-text">WOLF_SYSOP <span class="text-xs font-normal opacity-50">v3.0.4</span></h1>
                <p class="text-[10px] text-cyan-400 opacity-70 mt-1">STATUS: ENCRYPTED_TUNNEL_ACTIVE // UPTIME: <span id="stat-up">--:--:--</span></p>
            </div>
            <div class="flex gap-3">
                <button onclick="adminAction('reset_stats')" class="btn-cyber btn-cyan">PURGE_STATS</button>
                <button onclick="adminAction('shutdown')" class="btn-cyber btn-ban">TERMINATE_DAEMON</button>
            </div>
        </div>

        <div class="grid grid-cols-1 lg:grid-cols-4 gap-6">
            <div class="lg:col-span-3 space-y-6">
                <div class="grid grid-cols-1 md:grid-cols-3 gap-4">
                    <div class="cyber-panel p-4">
                        <div class="text-[9px] uppercase text-cyan-500 mb-1 tracking-widest">Aggregate Traffic</div>
                        <div class="text-2xl font-bold glow-text" id="stat-total">0 B</div>
                    </div>
                    <div class="cyber-panel p-4 border-l-2 border-l-[#ff0055]">
                        <div class="text-[9px] uppercase text-[#ff0055] mb-1 tracking-widest">Active Nodes</div>
                        <div class="text-2xl font-bold text-white" id="stat-count">0</div>
                    </div>
                    <div class="cyber-panel p-4">
                        <div class="text-[9px] uppercase text-cyan-500 mb-1 tracking-widest">Current Waveform</div>
                        <div class="text-2xl font-bold glow-text" id="stat-bps">0 B/s</div>
                    </div>
                </div>

                <div class="cyber-panel p-6">
                    <h2 class="text-xs mb-4 opacity-80">Traffic_Monitor_Stream</h2>
                    <div style="height: 200px;">
                        <canvas id="trafficChart"></canvas>
                    </div>
                </div>

                <div class="cyber-panel overflow-hidden">
                    <table class="w-full text-left text-xs">
                        <thead class="bg-cyan-950/30 text-cyan-400 uppercase font-bold border-b border-cyan-900/50">
                            <tr>
                                <th class="p-4">Identity</th>
                                <th class="p-4">Virtual_IP</th>
                                <th class="p-4">Origin_Source</th>
                                <th class="p-4">Payload_Stats</th>
                                <th class="p-4 text-right">Sanction</th>
                            </tr>
                        </thead>
                        <tbody id="peer-list" class="divide-y divide-cyan-900/20"></tbody>
                    </table>
                </div>
            </div>
            
            <div class="cyber-panel p-4 flex flex-col h-[600px]">
                <h2 class="text-[10px] glow-pink mb-4 italic tracking-tighter">>> SYSTEM_LOG_OUTPUT</h2>
                <div class="flex-1 overflow-y-auto font-mono text-[10px] space-y-1" id="log-container">
                    <div class="text-cyan-800">[00.00.00] INITIALIZING_CORE...</div>
                </div>
            </div>
        </div>
    </div>

    <script>
        const logContainer = document.getElementById('log-container');
        function addLog(msg, color) {
            if (!color) color = 'text-cyan-600';
            const time = new Date().toLocaleTimeString('en-GB', { hour12: false });
            const div = document.createElement('div');
            div.className = color;
            div.innerHTML = '[' + time + '] ' + msg;
            logContainer.prepend(div);
            if(logContainer.children.length > 50) logContainer.lastChild.remove();
        }

        async function update() {
            try {
                const r = await fetch("/api/stats");
                const d = await r.json();
                
                document.getElementById("stat-total").innerText = d.total;
                document.getElementById("stat-count").innerText = d.count;
                document.getElementById("stat-up").innerText = d.up;

                if (d.hist && d.hist.length > 0) {
                    const currentSpeed = d.hist[d.hist.length-1];
                    document.getElementById("stat-bps").innerText = formatBytes(currentSpeed) + "/s";
                    chart.data.datasets[0].data = d.hist;
                    chart.update('none');
                }

                const tbody = document.getElementById("peer-list");
                tbody.innerHTML = "";
                (d.peers || []).forEach(p => {
                    const row = document.createElement("tr");
                    row.className = "hover:bg-cyan-400/5 transition-colors";
                    
                    const statusClass = p.status === 'STABLE' ? 'text-cyan-400' : 'text-red-500 animate-pulse';
                    const lastSeenText = p.last_seen + 's ago';

                    row.innerHTML = 
                        '<td class="p-4">' +
                            '<div class="text-white font-bold tracking-widest">' + p.id + '</div>' +
                            '<div class="text-[9px] ' + statusClass + ' font-bold uppercase">' + p.status + ' (' + lastSeenText + ')</div>' +
                        '</td>' +
                        '<td class="p-4 text-cyan-400 font-bold">' + p.ip + '</td>' +
                        '<td class="p-4">' +
                            '<div class="flex items-center gap-2">' +
                                '<span class="text-lg">' + (p.flag || '🌐') + '</span>' +
                                '<div>' + 
                                    '<div class="text-white">' + p.ext_ip + '</div>' +
                                    '<div class="text-[9px] opacity-60">' + (p.city || 'Unknown_Sector') + '</div>' +
                                '</div>' +
                            '</div>' +
                        '</td>' +
                        '<td class="p-4 opacity-80">' +
                            'TX: <span class="text-cyan-400">' + p.tx + '</span><br>' +
                            'RX: <span class="text-pink-400">' + p.rx + '</span>' +
                        '</td>' +
                        '<td class="p-4 text-right space-x-2">' +
                            '<button onclick="adminAction(\'kick\', \'' + p.id + '\')" class="btn-cyber border-cyan-700 text-cyan-700 hover:text-cyan-300">KICK</button>' +
                            '<button onclick="adminAction(\'ban\', \'' + p.ext_ip + '\')" class="btn-cyber btn-ban">BANISH</button>' +
                        '</td>';
                    tbody.appendChild(row);
                });
            } catch(e) { console.error(e); }
        }

        function formatBytes(b) {
            if (b === 0) return '0 B';
            const i = Math.floor(Math.log(b) / Math.log(1024));
            return (b / Math.pow(1024, i)).toFixed(1) + ' ' + ['B', 'KB', 'MB', 'GB'][i];
        }

        const ctx = document.getElementById("trafficChart").getContext('2d');
        const gradient = ctx.createLinearGradient(0, 0, 0, 200);
        gradient.addColorStop(0, 'rgba(0, 242, 255, 0.3)');
        gradient.addColorStop(1, 'rgba(0, 242, 255, 0)');

        const chart = new Chart(ctx, {
            type: "line",
            data: {
                // Fix: Removed Go variable reference 'trafficHistory'
                labels: Array(60).fill(""), 
                datasets: [{ 
                    data: Array(60).fill(0), 
                    borderColor: "#00f2ff", 
                    borderWidth: 2,
                    pointRadius: 0,
                    tension: 0.4, 
                    fill: true,
                    backgroundColor: gradient
                }]
            },
            options: { 
                responsive: true,
                maintainAspectRatio: false,
                scales: { 
                    x: { display: false }, 
                    y: { 
                        beginAtZero: true,
                        grid: { color: 'rgba(0, 242, 255, 0.05)' },
                        ticks: { font: { size: 9 }, color: '#444' }
                    } 
                }, 
                plugins: { legend: false } 
            }
        });

        async function adminAction(a, t) {
            if (!t) t = "";
            addLog('EXECUTING_PROTOCOL: ' + a.toUpperCase() + ' -> ' + t, a === 'ban' ? 'text-pink-500' : 'text-cyan-400');
            await fetch('/api/admin?action=' + a + '&target=' + t);
            setTimeout(update, 500);
        }

        setInterval(update, 1000);
        addLog("VOICE_INTERFACE_READY", "text-cyan-400");
        addLog("NEURAL_LINK_ESTABLISHED", "text-cyan-400");
    </script>
</body>
</html>
`

func adminHandler(w http.ResponseWriter, r *http.Request) {
	action := r.URL.Query().Get("action")
	target := r.URL.Query().Get("target")

	switch action {
	case "ban":
		banMap.Store(target, time.Now().Add(1*time.Hour).Unix())
		// Iterate through sessions to find the one matching this external IP
		mgr.ByIdentity.Range(func(k, v interface{}) bool {
			s := v.(*UserSession)
			if strings.HasPrefix(s.Addr.String(), target) {
				mgr.ByIdentity.Delete(k)
				mgr.ByAddr.Delete(s.Addr.String())
				mgr.ByIP.Delete(s.InternalIP)
			}
			return true
		})
		fmt.Printf("[BANISH] %s exiled\n", target)

	case "kick":
		// Kick uses the Identity ID (first 8 chars or full)
		mgr.ByIdentity.Range(func(k, v interface{}) bool {
			id := k.(string)
			if strings.HasPrefix(id, target) {
				s := v.(*UserSession)
				mgr.ByIdentity.Delete(k)
				mgr.ByAddr.Delete(s.Addr.String())
				mgr.ByIP.Delete(s.InternalIP)
				return false
			}
			return true
		})

	case "reset_stats":
		// Reset the global counter
		atomic.StoreUint64(&totalBytes, 0)

		// Wipe the traffic history chart data
		historyMu.Lock()
		trafficHistory = make([]uint64, 60)
		historyMu.Unlock()

		// Optionally reset individual peer counters
		mgr.ByIdentity.Range(func(k, v interface{}) bool {
			s := v.(*UserSession)
			atomic.StoreUint64(&s.BytesIn, 0)
			atomic.StoreUint64(&s.BytesOut, 0)
			return true
		})
		fmt.Println("[SYS] Traffic statistics purged by administrator")

	case "shutdown":
		fmt.Println("[SYS] Daemon shutdown by administrator")
		os.Exit(0)
	}
	w.WriteHeader(http.StatusOK)
}

func updateGeoInfo(ip string) {
	if _, exists := geoCache.Load(ip); exists {
		return
	}

	// Using a 2-second timeout to prevent handshake lag
	client := http.Client{Timeout: 2 * time.Second}
	resp, err := client.Get(fmt.Sprintf("http://ip-api.com/json/%s?fields=status,countryCode,city", ip))
	if err != nil {
		return
	}
	defer resp.Body.Close()

	var res struct {
		Status  string `json:"status"`
		Country string `json:"countryCode"`
		City    string `json:"city"`
	}
	json.NewDecoder(resp.Body).Decode(&res)

	if res.Status == "success" {
		flagEmoji := ""
		if len(res.Country) == 2 {
			// Convert country code to regional indicator symbols
			flagEmoji = string(rune(res.Country[0])+127397) + string(rune(res.Country[1])+127397)
		}
		geoCache.Store(ip, GeoData{City: res.City, Country: res.Country, Flag: flagEmoji})
	}
}
