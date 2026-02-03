package main

import (
	"crypto/sha256"
	"encoding/binary"
	"flag"
	"fmt"
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
	"golang.org/x/crypto/chacha20"
)

const (
	MagicSignature  uint32 = 0xACE1FACE
	TUN_MTU                = 1300
	BMP_HEADER_SIZE        = 54
	OP_DATA         byte   = 4
	OP_AUTH         byte   = 5
	OP_HEARTBEAT    byte   = 6
	BAN_LIMIT              = 3
	BAN_TTL                = 3600
)

var (
	mgr                = &SessionManager{}
	conn               *net.UDPConn
	outboundChan       = make(chan outboundJob, 5000)
	origForwarding     string
	myAssignedIP       string
	cachedClientKey    []byte
	basePass           string
	clientSeq          uint32
	serverSeq          uint32
	sessionCount       int64
	lastServerActivity int64
	failCounter        = make(map[string]int)
	banList            = make(map[string]int64)
	securityLock       sync.RWMutex
	bufferPool         = sync.Pool{
		New: func() interface{} { return make([]byte, 65535) },
	}
)

type UserSession struct {
	Addr        *net.UDPAddr
	HWID        string
	InternalIP  string
	SeqIn       uint32
	SeqOut      uint32
	LastSeen    int64
	UserKey     []byte
	PacketCount uint64
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
	seq     uint32
	key     []byte
}

// --- FastBit Wolfram-XOR Implementation ---

func wolframChaCha(data []byte, key []byte, seq uint32) []byte {
	h := sha256.Sum256(binary.BigEndian.AppendUint32(key, seq))
	c, _ := chacha20.NewUnauthenticatedCipher(h[:32], h[20:32])
	seed := int64(binary.BigEndian.Uint64(h[:8]))
	rng := rand.New(rand.NewSource(seed))

	for i := range data {
		data[i] ^= uint8(rng.Intn(256))
	}
	c.XORKeyStream(data, data)
	return data
}

func encode6Bit(msg []byte, key []byte, seq uint32) []byte {
	payload := append(binary.BigEndian.AppendUint32(nil, MagicSignature), msg...)
	encrypted := wolframChaCha(payload, key, seq)
	vLen := uint32(len(encrypted))

	full := make([]byte, 8+len(encrypted))
	binary.BigEndian.PutUint32(full[0:4], vLen)
	binary.BigEndian.PutUint32(full[4:8], seq)
	copy(full[8:], encrypted)

	bmpBodyLen := (len(full)*8 + 5) / 6
	bmp := bufferPool.Get().([]byte)[:BMP_HEADER_SIZE+bmpBodyLen]

	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[2:6], uint32(len(bmp)))
	binary.LittleEndian.PutUint32(bmp[10:14], uint32(BMP_HEADER_SIZE))
	binary.LittleEndian.PutUint32(bmp[14:18], 40)
	binary.LittleEndian.PutUint32(bmp[18:22], uint32(bmpBodyLen/3))
	binary.LittleEndian.PutUint32(bmp[22:26], 1)
	binary.LittleEndian.PutUint16(bmp[26:28], 1)
	binary.LittleEndian.PutUint16(bmp[28:30], 24)

	var bitBuf uint64
	var bitCount uint
	cursor := BMP_HEADER_SIZE
	for _, b := range full {
		bitBuf = (bitBuf << 8) | uint64(b)
		bitCount += 8
		for bitCount >= 6 {
			bitCount -= 6
			bmp[cursor] = 0x40 | uint8((bitBuf>>bitCount)&0x3F)
			cursor++
		}
	}
	if bitCount > 0 {
		bmp[cursor] = 0x40 | uint8((bitBuf<<(6-bitCount))&0x3F)
	}
	return bmp
}

func decode6Bit(stego []byte, key []byte, seqPtr *uint32) ([]byte, bool) {
	if len(stego) < BMP_HEADER_SIZE+12 {
		return nil, false
	}
	rawLen := len(stego) - BMP_HEADER_SIZE
	bitStream := make([]byte, (rawLen*6)/8)
	var bitBuf uint64
	var bitCount uint
	writePtr := 0
	for i := 0; i < rawLen; i++ {
		bitBuf = (bitBuf << 6) | uint64(stego[BMP_HEADER_SIZE+i]&0x3F)
		bitCount += 6
		if bitCount >= 8 {
			bitCount -= 8
			if writePtr < len(bitStream) {
				bitStream[writePtr] = uint8(bitBuf >> bitCount)
				writePtr++
			}
		}
	}
	if len(bitStream) < 8 {
		return nil, false
	}
	vLen := binary.BigEndian.Uint32(bitStream[0:4])
	rSeq := binary.BigEndian.Uint32(bitStream[4:8])
	if vLen == 0 || int(8+vLen) > len(bitStream) {
		return nil, false
	}
	vault := bitStream[8 : 8+vLen]
	curr := atomic.LoadUint32(seqPtr)
	for o := -10; o <= 10; o++ {
		sSeq := uint32(int(rSeq) + o)
		testVault := append([]byte(nil), vault...)
		dec := wolframChaCha(testVault, key, sSeq)
		if len(dec) > 4 && binary.BigEndian.Uint32(dec[:4]) == MagicSignature {
			if sSeq >= curr {
				atomic.StoreUint32(seqPtr, sSeq+1)
			}
			return dec[4:], true
		}
	}
	return nil, false
}

// --- System Config & Security ---

func runCmd(c string, args ...string) { _ = exec.Command(c, args...).Run() }

func banIP(remoteAddr string) {
	host, _, _ := net.SplitHostPort(remoteAddr)
	securityLock.Lock()
	defer securityLock.Unlock()
	if _, banned := banList[host]; !banned {
		fmt.Printf("[!] Banning %s for 1 hour\n", host)
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
		for range time.Tick(2 * time.Second) {
			fmt.Print("\033[H\033[2J")
			fmt.Printf("=== VPN DASHBOARD [%s] ===\n", time.Now().Format("15:04:05"))
			if isServer {
				fmt.Printf("%-15s | %-15s | %-8s | %s\n", "INT IP", "REMOTE", "PKTS", "HWID")
				mgr.ByHWID.Range(func(k, v interface{}) bool {
					s := v.(*UserSession)
					fmt.Printf("%-15s | %-15s | %-8d | %s\n", s.InternalIP, s.Addr.String(), atomic.LoadUint64(&s.PacketCount), s.HWID)
					return true
				})
			} else {
				fmt.Printf("Status: Connected [%s] | Activity: %ds ago\n", myAssignedIP, time.Now().Unix()-atomic.LoadInt64(&lastServerActivity))
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
	fmt.Println("\n[*] Restoring networking...")
	securityLock.Lock()
	for ip := range banList {
		runCmd("iptables", "-D", "INPUT", "-s", ip, "-j", "DROP")
	}
	securityLock.Unlock()
	_ = exec.Command("mv", "/etc/resolv.conf.bak", "/etc/resolv.conf").Run()
	runCmd("iptables", "-D", "OUTPUT", "-j", "VPN_KILLSWITCH")
	runCmd("iptables", "-F", "VPN_KILLSWITCH")
	runCmd("iptables", "-X", "VPN_KILLSWITCH")
	runCmd("sysctl", "-w", "net.ipv4.ip_forward="+origFwd)
	os.Exit(0)
}

func getHWID() string {
	host, _ := os.Hostname()
	h := sha256.Sum256([]byte(host))
	return fmt.Sprintf("%x", h[:8])
}

// --- Main Engine ---

func main() {
	lPort := flag.String("l", "9000", "Local Port")
	tAddrStr := flag.String("t", "", "Target Host:Port")
	flag.StringVar(&basePass, "p", "BatMan", "Secret Key")
	tunIP := flag.String("ip", "10.0.0.1", "Internal IP")
	isServer := flag.Bool("server", false, "Server Mode")
	telemetry := flag.Bool("telemetry", false, "telemetry dashboard")
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
		go func() {
			for range time.Tick(30 * time.Second) {
				now := time.Now().Unix()
				mgr.ByHWID.Range(func(k, v interface{}) bool {
					s := v.(*UserSession)
					if now-atomic.LoadInt64(&s.LastSeen) > 300 {
						mgr.ByHWID.Delete(s.HWID)
						mgr.ByIP.Delete(s.InternalIP)
						mgr.ByAddr.Delete(s.Addr.String())
					}
					return true
				})
			}
		}()
	}

	if *telemetry {
		startTelemetry(*isServer)
	}

	for i := 0; i < runtime.NumCPU(); i++ {
		go func() {
			for job := range outboundChan {
				stego := encode6Bit(job.payload[:job.n], job.key, job.seq)
				conn.WriteToUDP(append([]byte{OP_DATA}, stego...), job.target)
				bufferPool.Put(job.payload)
				bufferPool.Put(stego[:cap(stego)])
			}
		}()

		go func() {
			for {
				buf := bufferPool.Get().([]byte)
				n, rem, err := conn.ReadFromUDP(buf)
				if err != nil {
					bufferPool.Put(buf)
					continue
				}
				atomic.StoreInt64(&lastServerActivity, time.Now().Unix())

				switch buf[0] {
				case OP_DATA:
					remoteStr := rem.String()
					var success bool
					if val, ok := mgr.ByAddr.Load(remoteStr); ok {
						s := val.(*UserSession)
						if dec, ok := decode6Bit(buf[1:n], s.UserKey, &s.SeqIn); ok {
							success = true
							atomic.StoreInt64(&s.LastSeen, time.Now().Unix())
							atomic.AddUint64(&s.PacketCount, 1)
							tun.Write(dec)
							securityLock.Lock()
							delete(failCounter, remoteStr)
							securityLock.Unlock()
						}
					} else if !*isServer && myAssignedIP != "" {
						if cachedClientKey == nil {
							k := sha256.Sum256([]byte(basePass + myAssignedIP))
							cachedClientKey = k[:]
						}
						if dec, ok := decode6Bit(buf[1:n], cachedClientKey, &serverSeq); ok {
							tun.Write(dec)
						}
					}
					if !success && *isServer {
						securityLock.Lock()
						failCounter[remoteStr]++
						if failCounter[remoteStr] >= BAN_LIMIT {
							banIP(remoteStr)
						}
						securityLock.Unlock()
					}
				case OP_AUTH:
					data := string(buf[1:n])
					if *isServer {
						var s *UserSession
						if val, ok := mgr.ByHWID.Load(data); ok {
							s = val.(*UserSession)
							mgr.ByAddr.Delete(s.Addr.String())
							s.Addr = rem
						} else {
							newIP := fmt.Sprintf("10.0.0.%d", 2+atomic.AddInt64(&sessionCount, 1)-1)
							k := sha256.Sum256([]byte(basePass + newIP))
							s = &UserSession{Addr: rem, HWID: data, InternalIP: newIP, UserKey: k[:], LastSeen: time.Now().Unix()}
							mgr.ByHWID.Store(data, s)
							mgr.ByIP.Store(newIP, s)
						}
						mgr.ByAddr.Store(rem.String(), s)
						conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(s.InternalIP)...), rem)
					} else {
						myAssignedIP = data
						runCmd("ip", "addr", "replace", data+"/24", "dev", tun.Name())
					}
				}
				bufferPool.Put(buf[:cap(buf)])
			}
		}()
	}

	target, _ := net.ResolveUDPAddr("udp", *tAddrStr)
	hwid := getHWID()
	go func() {
		for range time.Tick(5 * time.Second) {
			if !*isServer && *tAddrStr != "" {
				if time.Now().Unix()-atomic.LoadInt64(&lastServerActivity) > 15 {
					conn.WriteToUDP(append([]byte{OP_AUTH}, []byte(hwid)...), target)
				} else if myAssignedIP != "" {
					conn.WriteToUDP([]byte{OP_HEARTBEAT}, target)
				}
			}
		}
	}()

	for {
		pkt := bufferPool.Get().([]byte)
		n, err := tun.Read(pkt)
		if err != nil {
			bufferPool.Put(pkt)
			continue
		}
		if *isServer {
			if n < 20 {
				continue
			}
			destIP := net.IP(pkt[16:20]).String()
			if val, ok := mgr.ByIP.Load(destIP); ok {
				u := val.(*UserSession)
				outboundChan <- outboundJob{payload: pkt, n: n, target: u.Addr, seq: atomic.AddUint32(&u.SeqOut, 1) - 1, key: u.UserKey}
			} else {
				bufferPool.Put(pkt)
			}
		} else if myAssignedIP != "" {
			if cachedClientKey == nil {
				k := sha256.Sum256([]byte(basePass + myAssignedIP))
				cachedClientKey = k[:]
			}
			outboundChan <- outboundJob{payload: pkt, n: n, target: target, seq: atomic.AddUint32(&clientSeq, 1) - 1, key: cachedClientKey}
		}
	}
}
