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
	SESSION_TTL = 300
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
		go func() {
			for range time.Tick(1 * time.Second) {
				historyMu.Lock()
				trafficHistory = append(trafficHistory, atomic.LoadUint64(&totalBytes))
				if len(trafficHistory) > 60 {
					trafficHistory = trafficHistory[1:]
				}
				historyMu.Unlock()
			}
		}()

		http.HandleFunc("/api/stats", func(w http.ResponseWriter, r *http.Request) {
			type PeerStat struct {
				ID       string `json:"id"`
				IP       string `json:"ip"`
				Ext      string `json:"ext"`
				TX       string `json:"tx"`
				RX       string `json:"rx"`
				LastSeen int64  `json:"lastSeen"`
			}
			peers := []PeerStat{}
			mgr.ByIdentity.Range(func(k, v interface{}) bool {
				s := v.(*UserSession)
				peers = append(peers, PeerStat{
					ID: k.(string)[:12], IP: s.InternalIP, Ext: s.Addr.String(),
					TX: formatBytes(atomic.LoadUint64(&s.BytesOut)), RX: formatBytes(atomic.LoadUint64(&s.BytesIn)),
					LastSeen: time.Now().Unix() - atomic.LoadInt64(&s.LastSeen),
				})
				return true
			})

			historyMu.RLock()
			defer historyMu.RUnlock()
			w.Header().Set("Content-Type", "application/json")
			json.NewEncoder(w).Encode(map[string]interface{}{
				"totalBytes": formatBytes(atomic.LoadUint64(&totalBytes)),
				"peerCount":  len(peers),
				"peers":      peers,
				"history":    trafficHistory,
				"uptime":     time.Since(startTime).Truncate(time.Second).String(),
			})
		})

		http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
			w.Header().Set("Content-Type", "text/html")
			fmt.Fprint(w, `
			<!DOCTYPE html>
			<html>
			<head>
				<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
				<script src="https://cdn.tailwindcss.com"></script>
				<script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
				<title>Wolf VPN</title>
				<style>
					body { background: #0b0f1a; color: #e2e8f0; font-family: sans-serif; }
					.glass { background: rgba(23, 32, 53, 0.8); backdrop-filter: blur(12px); border: 1px solid rgba(255,255,255,0.05); }
				</style>
			</head>
			<body class="p-4 md:p-10">
				<div class="max-w-6xl mx-auto">
					<header class="flex justify-between items-center mb-10">
						<h1 class="text-3xl font-black italic text-blue-400">WOLF_VPN</h1>
						<div class="glass px-4 py-2 rounded-xl text-xs font-mono text-slate-400" id="clock">--:--:--</div>
					</header>
					<div class="grid grid-cols-1 lg:grid-cols-3 gap-6 mb-10">
						<div class="lg:col-span-2 glass p-6 rounded-3xl">
							<h3 class="text-slate-500 text-xs font-bold uppercase mb-4 tracking-widest">Network Throughput</h3>
							<div class="h-48"><canvas id="trafficChart"></canvas></div>
						</div>
						<div class="grid grid-cols-1 gap-4">
							<div class="glass p-6 rounded-2xl border-l-4 border-blue-500">
								<h3 class="text-slate-500 text-xs font-bold uppercase mb-1">Total Data</h3>
								<p class="text-2xl font-mono font-bold" id="stat-total">0 B</p>
							</div>
							<div class="glass p-6 rounded-2xl border-l-4 border-emerald-500">
								<h3 class="text-slate-500 text-xs font-bold uppercase mb-1">Active Peers</h3>
								<p class="text-2xl font-mono font-bold" id="stat-peers">0</p>
							</div>
							<div class="glass p-6 rounded-2xl border-l-4 border-purple-500">
								<h3 class="text-slate-500 text-xs font-bold uppercase mb-1">Uptime</h3>
								<p class="text-2xl font-mono font-bold" id="stat-uptime">0s</p>
							</div>
						</div>
					</div>
					<div class="glass rounded-3xl overflow-hidden">
						<table class="w-full text-left">
							<thead class="bg-white/5 text-[10px] uppercase text-slate-500 tracking-widest">
								<tr><th class="px-8 py-4">Peer ID</th><th class="px-8 py-4">Internal IP</th><th class="px-8 py-4">External IP</th><th class="px-8 py-4">TX/RX</th><th class="px-8 py-4 text-right">Status</th></tr>
							</thead>
							<tbody id="peer-list" class="divide-y divide-white/5"></tbody>
						</table>
					</div>
				</div>
				<script>
					const ctx = document.getElementById('trafficChart').getContext('2d');
					const chart = new Chart(ctx, {
						type: 'line',
						data: {
							labels: Array(60).fill(''),
							datasets: [{
								data: [], borderColor: '#60a5fa', backgroundColor: 'rgba(96, 165, 250, 0.1)',
								fill: true, tension: 0.4, pointRadius: 0
							}]
						},
						options: { 
							responsive: true, maintainAspectRatio: false,
							plugins: { legend: { display: false } },
							scales: { x: { display: false }, y: { grid: { color: 'rgba(255,255,255,0.05)' }, ticks: { color: '#64748b', font: { size: 10 } } } }
						}
					});

					async function updateStats() {
						try {
							const res = await fetch('/api/stats');
							const data = await res.json();
							if (!data) return;

							document.getElementById('stat-total').innerText = data.totalBytes || '0 B';
							document.getElementById('stat-peers').innerText = data.peerCount || 0;
							document.getElementById('stat-uptime').innerText = data.uptime || '0s';
							document.getElementById('clock').innerText = new Date().toLocaleTimeString();

							chart.data.datasets[0].data = data.history || [];
							chart.update('none');

							const tbody = document.getElementById('peer-list');
							const peers = data.peers || [];
							if (peers.length === 0) {
								tbody.innerHTML = '<tr><td colspan="5" class="p-8 text-center text-slate-600 italic">No peers connected</td></tr>';
							} else {
								tbody.innerHTML = peers.map(function(p) {
									return '<tr class="hover:bg-white/5 transition-colors">' +
										'<td class="px-8 py-5 font-mono text-xs text-blue-300">' + p.id + '...</td>' +
										'<td class="px-8 py-5"><span class="bg-emerald-500/10 text-emerald-400 px-2 py-1 rounded text-sm font-mono">' + p.ip + '</span></td>' +
										'<td class="px-8 py-5 font-mono text-xs text-slate-500">' + p.ext + '</td>' +
										'<td class="px-8 py-5 text-xs font-mono text-slate-400">↑' + p.tx + ' ↓' + p.rx + '</td>' +
										'<td class="px-8 py-5 text-right font-bold text-xs ' + (p.lastSeen < 30 ? 'text-emerald-400' : 'text-amber-500') + '">' + p.lastSeen + 's ago</td>' +
									'</tr>';
								}).join('');
							}
						} catch (e) { console.error("Stats fetch failed", e); }
					}
					setInterval(updateStats, 1000);
					updateStats();
				</script>
			</body>
			</html>`)
		})
		go http.ListenAndServe(fmt.Sprintf(":%d", *apiPort), nil)
	}

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
								atomic.AddUint64(&s.BytesIn, uint64(n))
								atomic.AddUint64(&totalBytes, uint64(n))
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
								s.Addr = rem // Update external IP if it changed
							} else {
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

	for {
		pkt := make([]byte, 2048)
		n, _ := tun.Read(pkt)
		tx := make([]byte, 2048)
		tx[0] = OP_DATA
		if *isServer && n >= 20 {
			destIP := net.IP(pkt[16:20]).String()
			if val, ok := mgr.ByIP.Load(destIP); ok {
				s := val.(*UserSession)
				encrypted := sealPacket(tx, s.AEAD, atomic.AddUint64(&s.SeqOut, 1), pkt[:n])
				conn.WriteToUDP(encrypted, s.Addr)
				atomic.AddUint64(&s.BytesOut, uint64(len(encrypted)))
				atomic.AddUint64(&totalBytes, uint64(len(encrypted)))
			}
		} else if !*isServer {
			if val := clientAEAD.Load(); val != nil && currentTarget != nil {
				conn.WriteToUDP(sealPacket(tx, val.(cipher.AEAD), atomic.AddUint64(&clientSeq, 1), pkt[:n]), currentTarget)
			}
		}
	}
}
