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
	pass := flag.String("p", "WolfPass", "Secret")
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

		http.HandleFunc("/api/stats", func(w http.ResponseWriter, r *http.Request) {
			peers := []PeerStat{}
			mgr.ByIdentity.Range(func(k, v interface{}) bool {
				s := v.(*UserSession)
				ls := atomic.LoadInt64(&s.LastSeen)
				status := "STABLE"
				if time.Now().Unix()-ls > 20 {
					status = "LAGGING"
				}

				peers = append(peers, PeerStat{
					ID:     k.(string)[:8],
					IP:     s.InternalIP,
					TX:     formatBytes(atomic.LoadUint64(&s.BytesOut)),
					RX:     formatBytes(atomic.LoadUint64(&s.BytesIn)),
					LT:     time.Now().Unix() - ls,
					Status: status,
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
				"gr":    runtime.NumGoroutine(),
			})
		})

		http.HandleFunc("/api/admin", adminHandler)
		http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
			w.Header().Set("Content-Type", "text/html")
			fmt.Fprint(w, dashboardHTML)
		})

		fmt.Printf("[WEB] Dashboard active on :%d\n", *apiPort)
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
							var s *UserSession
							if val, ok := mgr.ByIdentity.Load(id); ok {
								s = val.(*UserSession)
								s.Addr = rem
							} else {
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
								fmt.Printf("[AUTH] Peer %s @ %s\n", id[:8], s.InternalIP)
							}
						}
					} else if !*isServer && n >= 33 {
						var sp [32]byte
						copy(sp[:], buf[1:33])
						clientAEAD.Store(func() cipher.AEAD { a, _ := chacha20poly1305.New(deriveKey(myPriv, sp)); return a }())
						assignedIP := string(buf[33:n])

						fmt.Println("[AUTH] Handshake success. Configuring tunnel...")
						runCmd("ip", "addr", "replace", assignedIP+"/24", "dev", tun.Name())

						// --- FIX: PIN SERVER IP TO PHYSICAL GATEWAY ---
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
							serverIP := currentTarget.IP.String()
							runCmd("ip", "route", "add", serverIP, "via", gateway)
							fmt.Printf("[SYS] Pinned server %s via physical gateway %s\n", serverIP, gateway)
						}

						// --- REDIRECT ALL TRAFFIC ---
						runCmd("ip", "route", "add", "0.0.0.0/1", "dev", tun.Name())
						runCmd("ip", "route", "add", "128.0.0.0/1", "dev", tun.Name())

						// --- DNS PROTECTION ---
						runCmd("resolvectl", "dns", tun.Name(), "8.8.8.8")
						runCmd("resolvectl", "domain", tun.Name(), "~.")

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

				sent := uint64(len(encrypted))
				atomic.AddUint64(&s.BytesOut, sent)
				atomic.AddUint64(&totalBytes, sent)
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
        @import url('https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;700&display=swap');
        body { background: #020408; color: #94a3b8; font-family: 'JetBrains Mono', monospace; }
        .panel { background: #0f172a; border: 1px solid #1e293b; }
        .chart-box { position: relative; height: 180px; width: 100%; }
        .btn-sys { padding: 4px 12px; border-radius: 4px; font-size: 10px; font-weight: bold; text-transform: uppercase; border: 1px solid transparent; cursor: pointer; }
        .btn-danger { color: #ef4444; border-color: #450a0a; background: #1a0505; }
        .btn-primary { color: #3b82f6; border-color: #1e3a8a; background: #0f172a; }
    </style>
</head>
<body class="p-4">
    <div class="max-w-7xl mx-auto">
        <div class="flex justify-between items-center mb-6 bg-slate-900/50 p-4 border border-slate-800 rounded-lg">
            <h1 class="text-white font-black italic text-xl">WOLF_SYSOP</h1>
            <div class="flex gap-2">
                <button onclick="adminAction('reset_stats')" class="btn-sys btn-primary">Reset Stats</button>
                <button onclick="adminAction('shutdown')" class="btn-sys btn-danger">Shutdown</button>
            </div>
        </div>

        <div class="grid grid-cols-1 lg:grid-cols-4 gap-6">
            <div class="lg:col-span-3 space-y-6">
                <div class="grid grid-cols-2 md:grid-cols-4 gap-4">
                    <div class="panel p-4 rounded-lg">
                        <div class="text-[9px] uppercase mb-1">Total Traffic</div>
                        <div class="text-xl text-white font-bold" id="stat-total">0 B</div>
                    </div>
                    <div class="panel p-4 rounded-lg border-l-2 border-l-blue-500">
                        <div class="text-[9px] uppercase mb-1">Current Speed</div>
                        <div class="text-xl text-white font-bold" id="stat-bps">0 B/s</div>
                    </div>
                </div>

                <div class="panel p-6 rounded-xl">
                    <canvas id="trafficChart"></canvas>
                </div>

                <div class="panel rounded-xl overflow-hidden">
                    <table class="w-full text-left text-xs">
                        <thead class="bg-slate-800/40 text-slate-500 uppercase">
                            <tr>
                                <th class="p-4">Identity</th>
                                <th class="p-4">IP</th>
                                <th class="p-4">Stats</th>
                                <th class="p-4 text-right">Action</th>
                            </tr>
                        </thead>
                        <tbody id="peer-list"></tbody>
                    </table>
                </div>
            </div>
            
            <div class="panel rounded-xl p-4 text-[10px] font-mono h-[400px] overflow-y-auto" id="log-container">
                <div class="text-slate-600 italic">SYSTEM READY...</div>
            </div>
        </div>
    </div>

    <script>
        // Use standard string concatenation to avoid backtick issues in some Go versions
        async function update() {
            try {
                const r = await fetch("/api/stats");
                const d = await r.json();
                
                document.getElementById("stat-total").innerText = d.total;
                if (d.hist && d.hist.length > 0) {
                    document.getElementById("stat-bps").innerText = formatBytes(d.hist[d.hist.length-1]) + "/s";
                    chart.data.datasets[0].data = d.hist;
                    chart.update('none');
                }

                const tbody = document.getElementById("peer-list");
                tbody.innerHTML = "";
                (d.peers || []).forEach(p => {
                    const row = document.createElement("tr");
                    row.className = "border-b border-slate-800/30";
                    row.innerHTML = '<td class="p-4 text-white font-bold">' + p.id + '</td>' +
                                  '<td class="p-4 text-blue-400">' + p.ip + '</td>' +
                                  '<td class="p-4">TX ' + p.tx + ' / RX ' + p.rx + '</td>' +
                                  '<td class="p-4 text-right"><button onclick="adminAction(\'kick\', \'' + p.id + '\')" class="btn-sys btn-danger">Kick</button></td>';
                    tbody.appendChild(row);
                });
            } catch(e) { console.error(e); }
        }

        function formatBytes(b) {
            if (b === 0) return '0 B';
            const i = Math.floor(Math.log(b) / Math.log(1024));
            return (b / Math.pow(1024, i)).toFixed(1) + ' ' + ['B', 'KB', 'MB', 'GB'][i];
        }

        const chart = new Chart(document.getElementById("trafficChart"), {
            type: "line",
            data: {
                labels: Array(60).fill(""),
                datasets: [{ data: Array(60).fill(0), borderColor: "#3b82f6", tension: 0.3, fill: true }]
            },
            options: { scales: { x: { display: false }, y: { beginAtZero: true } }, plugins: { legend: false } }
        });

        async function adminAction(a, t="") {
            await fetch("/api/admin?action=" + a + "&target=" + t);
            update();
        }

        setInterval(update, 1000);
    </script>
</body>
</html>
`

func adminHandler(w http.ResponseWriter, r *http.Request) {
	action := r.URL.Query().Get("action")
	target := r.URL.Query().Get("target")

	switch action {
	case "kick":
		// Iterate through sessions to find the one matching the prefix
		mgr.ByIdentity.Range(func(k, v interface{}) bool {
			if strings.HasPrefix(k.(string), target) {
				s := v.(*UserSession)
				// Remove from all lookup maps
				mgr.ByIdentity.Delete(k)
				mgr.ByAddr.Delete(s.Addr.String())
				mgr.ByIP.Delete(s.InternalIP)
				fmt.Printf("[ADMIN] Kicked peer: %s\n", k.(string)[:8])
				return false // Stop iterating
			}
			return true
		})

	case "reset_stats":
		// Reset global counter
		atomic.StoreUint64(&totalBytes, 0)
		// Reset individual peer counters
		mgr.ByIdentity.Range(func(k, v interface{}) bool {
			s := v.(*UserSession)
			atomic.StoreUint64(&s.BytesIn, 0)
			atomic.StoreUint64(&s.BytesOut, 0)
			return true
		})
		fmt.Println("[ADMIN] Statistics have been reset")

	case "shutdown":
		fmt.Println("[ADMIN] Remote shutdown initiated")
		cleanup(true) // This calls your existing cleanup logic
	}

	w.WriteHeader(http.StatusOK)
}
