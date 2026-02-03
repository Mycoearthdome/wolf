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

const (
	TUN_MTU      = 1350
	OP_DATA      = 4
	OP_AUTH      = 5
	OP_KEEPALIVE = 6
	BAN_LIMIT    = 3
	BAN_TTL      = 3600
)

var (
	mgr                = &SessionManager{}
	conn               *net.UDPConn
	outboundChan       = make(chan outboundJob, 10000)
	origForwarding     string
	myAssignedIP       string
	cachedClientKey    []byte
	basePass           string
	clientSeq          uint64
	serverSeq          uint64
	sessionCount       int64
	lastServerActivity int64
	ingressPackets     uint64
	egressPackets      uint64
	failCounter        = make(map[string]int)
	banList            = make(map[string]int64)
	securityLock       sync.RWMutex
	bufferPool         = sync.Pool{
		New: func() interface{} { return make([]byte, 2048) },
	}
)

type UserSession struct {
	Addr       *net.UDPAddr
	HWID       string
	InternalIP string
	SeqOut     uint64
	LastSeen   int64
	UserKey    []byte
	AEAD       cipher.AEAD
	PktsIn     uint64
	PktsOut    uint64
}

type SessionManager struct {
	ByIP   sync.Map
	ByAddr sync.Map
	ByHWID sync.Map
}

type outboundJob struct {
	payload []byte
	n       int
	target  *net.UDPAddr
	seq     uint64
	aead    cipher.AEAD
}

// --- High-Speed Crypto ---

func fastWrap(data []byte, aead cipher.AEAD, seq uint64) []byte {
	nonce := make([]byte, aead.NonceSize())
	binary.BigEndian.PutUint64(nonce, seq)
	return aead.Seal(nonce, nonce, data, nil)
}

func fastUnwrap(raw []byte, aead cipher.AEAD) ([]byte, error) {
	if len(raw) < 24 {
		return nil, fmt.Errorf("packet short")
	}
	nonce := raw[:aead.NonceSize()]
	return aead.Open(nil, nonce, raw[aead.NonceSize():], nil)
}

// --- System Config & Security ---

func runCmd(c string, args ...string) { _ = exec.Command(c, args...).Run() }

func banIP(remoteAddr string) {
	host, _, _ := net.SplitHostPort(remoteAddr)
	securityLock.Lock()
	defer securityLock.Unlock()
	if _, banned := banList[host]; !banned {
		runCmd("iptables", "-I", "INPUT", "1", "-s", host, "-j", "DROP")
		banList[host] = time.Now().Unix() + BAN_TTL
	}
}

func manageBans() {
	go func() {
		for range time.Tick(60 * time.Second) {
			now := time.Now().Unix()
			securityLock.Lock()
			for ip, expiry := range banList {
				if now >= expiry {
					runCmd("iptables", "-D", "INPUT", "-s", ip, "-j", "DROP")
					delete(banList, ip)
					delete(failCounter, ip)
				}
			}
			securityLock.Unlock()
		}
	}()
}

func startTelemetry(isServer bool) {
	go func() {
		for range time.Tick(time.Second) {
			fmt.Print("\033[H\033[2J") // Clear screen
			fmt.Printf("=== VPN TELEMETRY [%s] ===\n", time.Now().Format("15:04:05"))
			fmt.Printf("Global Ingress: %d | Global Egress: %d\n", atomic.LoadUint64(&ingressPackets), atomic.LoadUint64(&egressPackets))
			fmt.Println(strings.Repeat("-", 60))

			if isServer {
				fmt.Printf("%-15s | %-18s | %-8s | %-8s | %-10s\n", "INTERNAL IP", "REMOTE ADDR", "IN", "OUT", "STATUS")
				mgr.ByHWID.Range(func(k, v interface{}) bool {
					s := v.(*UserSession)
					status := "ACTIVE"
					if time.Now().Unix()-atomic.LoadInt64(&s.LastSeen) > 30 {
						status = "STALE"
					}
					fmt.Printf("%-15s | %-18s | %-8d | %-8d | %-10s\n", s.InternalIP, s.Addr.String(), atomic.LoadUint64(&s.PktsIn), atomic.LoadUint64(&s.PktsOut), status)
					return true
				})
			} else {
				lastSeen := time.Now().Unix() - atomic.LoadInt64(&lastServerActivity)
				status := "CONNECTED"
				if lastSeen > 30 {
					status = "RECONNECTING"
				}
				fmt.Printf("Assigned IP: %s\n", myAssignedIP)
				fmt.Printf("Gateway Status: %s (Last activity: %ds ago)\n", status, lastSeen)
			}
		}
	}()
}

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
		runCmd("iptables", "-A", "FORWARD", "-i", name, "-j", "ACCEPT")
	} else if localIP != "0.0.0.0" && peerIP != "" {
		runCmd("ip", "route", "add", peerIP, "via", gw, "dev", dev, "metric", "1")
		_ = exec.Command("mv", "/etc/resolv.conf", "/etc/resolv.conf.bak").Run()
		_ = exec.Command("bash", "-c", "echo 'nameserver 8.8.8.8' > /etc/resolv.conf").Run()
		runCmd("iptables", "-N", "VPN_KILLSWITCH")
		runCmd("iptables", "-I", "OUTPUT", "1", "-j", "VPN_KILLSWITCH")
		runCmd("iptables", "-A", "VPN_KILLSWITCH", "-d", peerIP, "-p", "udp", "-j", "ACCEPT")
		runCmd("iptables", "-A", "VPN_KILLSWITCH", "-o", name, "-j", "ACCEPT")
		runCmd("iptables", "-A", "VPN_KILLSWITCH", "-j", "DROP")
		runCmd("ip", "route", "add", "0.0.0.0/1", "dev", name, "metric", "5")
		runCmd("ip", "route", "add", "128.0.0.0/1", "dev", name, "metric", "5")
	}
	return gw, dev
}

func cleanup(origFwd string) {
	_ = exec.Command("mv", "/etc/resolv.conf.bak", "/etc/resolv.conf").Run()
	runCmd("iptables", "-D", "OUTPUT", "-j", "VPN_KILLSWITCH")
	runCmd("sysctl", "-w", "net.ipv4.ip_forward="+origFwd)
	os.Exit(0)
}

// --- Main Engine ---

func main() {
	lPort := flag.String("l", "9000", "Local Port")
	tAddrStr := flag.String("t", "", "Target Host:Port")
	flag.StringVar(&basePass, "p", "Batman", "Secret Key")
	tunIP := flag.String("ip", "10.0.0.1", "Internal IP")
	isServer := flag.Bool("server", false, "Server Mode")
	telemetry := flag.Bool("telemetry", false, "Enable Dashboard")
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
	go func() { <-sig; cleanup(origForwarding) }()

	lAddr, _ := net.ResolveUDPAddr("udp", ":"+*lPort)
	conn, _ = net.ListenUDP("udp", lAddr)

	if *isServer {
		manageBans()
	}
	if *telemetry {
		startTelemetry(*isServer)
	}

	target, _ := net.ResolveUDPAddr("udp", *tAddrStr)
	host, _ := os.Hostname()

	// Workers
	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for job := range outboundChan {
				wrapped := fastWrap(job.payload[:job.n], job.aead, job.seq)
				conn.WriteToUDP(append([]byte{OP_DATA}, wrapped...), job.target)
				atomic.AddUint64(&egressPackets, 1)
				bufferPool.Put(job.payload)
			}
		}()

		go func() {
			for {
				buf := bufferPool.Get().([]byte)
				n, rem, err := conn.ReadFromUDP(buf)
				if err != nil || n < 1 {
					bufferPool.Put(buf)
					continue
				}

				switch buf[0] {
				case OP_DATA:
					var aead cipher.AEAD
					if *isServer {
						if val, ok := mgr.ByAddr.Load(rem.String()); ok {
							s := val.(*UserSession)
							aead = s.AEAD
							atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
							atomic.AddUint64(&s.PktsIn, 1)
						}
					} else if cachedClientKey != nil {
						aead, _ = chacha20poly1305.New(cachedClientKey)
						atomic.StoreInt64(&lastServerActivity, time.Now().Unix())
					}
					if aead != nil {
						if dec, err := fastUnwrap(buf[1:n], aead); err == nil {
							atomic.AddUint64(&ingressPackets, 1)
							tun.Write(dec)
						}
					}
				case OP_KEEPALIVE:
					if *isServer {
						if val, ok := mgr.ByAddr.Load(rem.String()); ok {
							s := val.(*UserSession)
							atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
							conn.WriteToUDP([]byte{OP_KEEPALIVE}, rem)
						}
					} else {
						atomic.StoreInt64(&lastServerActivity, time.Now().Unix())
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
							key := sha256.Sum256([]byte(basePass + newIP))
							aead, _ := chacha20poly1305.New(key[:])
							s = &UserSession{Addr: rem, HWID: hwid, InternalIP: newIP, UserKey: key[:], AEAD: aead}
							mgr.ByHWID.Store(hwid, s)
							mgr.ByIP.Store(newIP, s)
						}
						mgr.ByAddr.Store(rem.String(), s)
						atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
						conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(s.InternalIP)...), rem)
					} else {
						myAssignedIP = string(buf[1:n])
						k := sha256.Sum256([]byte(basePass + myAssignedIP))
						cachedClientKey = k[:]
						runCmd("ip", "addr", "replace", myAssignedIP+"/24", "dev", tun.Name())
						atomic.StoreInt64(&lastServerActivity, time.Now().Unix())
					}
				}
				bufferPool.Put(buf[:cap(buf)])
			}
		}()
	}

	// Keepalive
	go func() {
		for range time.Tick(10 * time.Second) {
			if !*isServer && *tAddrStr != "" {
				now := time.Now().Unix()
				if now-atomic.LoadInt64(&lastServerActivity) > 30 || myAssignedIP == "" {
					conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(host)...), target)
				} else {
					conn.WriteToUDP([]byte{OP_KEEPALIVE}, target)
				}
			}
		}
	}()

	for {
		pkt := bufferPool.Get().([]byte)
		n, err := tun.Read(pkt)
		if err != nil {
			continue
		}
		if *isServer {
			if n < 20 {
				continue
			}
			destIP := net.IP(pkt[16:20]).String()
			if val, ok := mgr.ByIP.Load(destIP); ok {
				u := val.(*UserSession)
				atomic.AddUint64(&u.PktsOut, 1)
				outboundChan <- outboundJob{payload: pkt, n: n, target: u.Addr, seq: atomic.AddUint64(&u.SeqOut, 1), aead: u.AEAD}
			}
		} else if cachedClientKey != nil {
			aead, _ := chacha20poly1305.New(cachedClientKey)
			outboundChan <- outboundJob{payload: pkt, n: n, target: target, seq: atomic.AddUint64(&clientSeq, 1), aead: aead}
		}
	}
}
