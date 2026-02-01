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
	"os/exec"
	"runtime"
	"sync"
	"sync/atomic"

	"github.com/songgao/water"
)

const (
	MagicSignature  uint32 = 0xACE1FACE
	ChunkSize              = 1400 // Optimized for standard MTU
	TUN_MTU                = 600  // Higher MTU possible with LSB4
	VaultWidth             = 256
	VaultHeight            = 128
	BMP_HEADER_SIZE        = 1078
)

var (
	state       *SessionState
	conn        *net.UDPConn
	tAddr       *net.UDPAddr
	tMu         sync.RWMutex
	frags       = &FragMan{Sess: make(map[uint32]*FileSess)}
	encryptChan = make(chan encryptJob, 512)
	tunDevice   *water.Interface
	keyCache    = make(map[uint32]cachedKey)
	cacheMu     sync.RWMutex
)

type encryptJob struct {
	payload []byte
	seq     uint32
}

type cachedKey struct {
	rule int
	pass string
}

type SessionState struct {
	BaseRule int
	BasePass string
	Seq      uint32
}

type FileSess struct {
	mu       sync.Mutex
	Data     [][]byte
	Received int
	Total    int
}

type FragMan struct {
	mu   sync.Mutex
	Sess map[uint32]*FileSess
}

func (f *FragMan) Add(sID, tot, idx uint32, d []byte) []byte {
	f.mu.Lock()
	defer f.mu.Unlock()
	fs, ok := f.Sess[sID]
	if !ok {
		fs = &FileSess{Data: make([][]byte, tot), Total: int(tot)}
		f.Sess[sID] = fs
	}
	fs.mu.Lock()
	defer fs.mu.Unlock()
	if idx >= uint32(len(fs.Data)) || fs.Data[idx] != nil {
		return nil
	}
	fs.Data[idx] = d
	fs.Received++
	if fs.Received == fs.Total {
		res := bytes.Join(fs.Data, nil)
		delete(f.Sess, sID)
		return res
	}
	return nil
}

// --- Turbo Stego Logic ---

func getKeys(basePass string, baseRule int, seq uint32) (int, string) {
	cacheMu.RLock()
	if val, ok := keyCache[seq]; ok {
		cacheMu.RUnlock()
		return val.rule, val.pass
	}
	cacheMu.RUnlock()

	h := sha256.Sum256([]byte(fmt.Sprintf("%s-%d", basePass, seq)))
	r := (baseRule + int(seq)) % 2187
	if r < 0 {
		r = -r
	}
	pass := fmt.Sprintf("%x", h)

	cacheMu.Lock()
	if len(keyCache) > 1000 {
		for k := range keyCache {
			if k < seq-500 {
				delete(keyCache, k)
			}
		}
	}
	keyCache[seq] = cachedKey{rule: r, pass: pass}
	cacheMu.Unlock()
	return r, pass
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

func createVault(raw []byte, r int, p string) []byte {
	var b bytes.Buffer
	zw := gzip.NewWriter(&b)
	zw.Write(raw)
	zw.Close()

	payload := append(binary.BigEndian.AppendUint32(nil, MagicSignature), b.Bytes()...)
	return xor(payload, p)
}

func encode(msg []byte, r int, p string, seq uint32) []byte {
	vault := createVault(msg, r, p)
	const imgDataSize = 256 * 256
	const totalSize = BMP_HEADER_SIZE + imgDataSize
	bmp := make([]byte, totalSize)

	// Static BMP Header (Grayscale 8-bit)
	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[2:6], uint32(totalSize))
	binary.LittleEndian.PutUint32(bmp[10:14], BMP_HEADER_SIZE)
	binary.LittleEndian.PutUint32(bmp[14:18], 40)
	binary.LittleEndian.PutUint32(bmp[18:22], 256)
	binary.LittleEndian.PutUint32(bmp[22:26], 256)
	binary.LittleEndian.PutUint16(bmp[26:28], 1)
	binary.LittleEndian.PutUint16(bmp[28:30], 8)

	for i := 0; i < 256; i++ {
		off := 54 + (i * 4)
		bmp[off], bmp[off+1], bmp[off+2] = uint8(i), uint8(i), uint8(i)
	}

	rand.New(rand.NewSource(int64(seq))).Read(bmp[BMP_HEADER_SIZE:])

	// LSB4 Header Injection (VaultLen + Seq)
	hdr := binary.BigEndian.AppendUint32(binary.BigEndian.AppendUint32(nil, uint32(len(vault))), seq)
	for i := 0; i < 16; i++ {
		bmp[BMP_HEADER_SIZE+i] = (bmp[BMP_HEADER_SIZE+i] & 0xF0) | ((hdr[i/2] >> (uint(i%2) * 4)) & 0x0F)
	}

	// LSB4 Vault Injection
	for i := 0; i < len(vault)*2; i++ {
		bmp[BMP_HEADER_SIZE+16+i] = (bmp[BMP_HEADER_SIZE+16+i] & 0xF0) | ((vault[i/2] >> (uint(i%2) * 4)) & 0x0F)
	}
	return bmp
}

func decode(stego []byte, r int, p string) ([]byte, uint32, bool) {
	if len(stego) < BMP_HEADER_SIZE+16 {
		return nil, 0, false
	}

	var hdr [8]byte
	for i := 0; i < 16; i++ {
		hdr[i/2] |= (stego[BMP_HEADER_SIZE+i] & 0x0F) << (uint(i%2) * 4)
	}
	vLen := binary.BigEndian.Uint32(hdr[:4])
	seq := binary.BigEndian.Uint32(hdr[4:8])

	if vLen > 30000 || vLen == 0 {
		return nil, 0, false
	}

	vault := make([]byte, vLen)
	for i := 0; i < int(vLen)*2; i++ {
		vault[i/2] |= (stego[BMP_HEADER_SIZE+16+i] & 0x0F) << (uint(i%2) * 4)
	}

	f := xor(vault, p)
	if len(f) > 4 && binary.BigEndian.Uint32(f[:4]) == MagicSignature {
		zr, err := gzip.NewReader(bytes.NewReader(f[4:]))
		if err == nil {
			dec, _ := io.ReadAll(zr)
			zr.Close()
			return dec, seq, true
		}
	}
	return nil, 0, false
}

// --- Networking ---

func configureInterface(name, localIP string) {
	_ = exec.Command("ip", "link", "set", "dev", name, "up", "mtu", fmt.Sprintf("%d", TUN_MTU)).Run()
	_ = exec.Command("ip", "addr", "add", localIP+"/24", "dev", name).Run()
}

func worker() {
	for job := range encryptChan {
		r, p := getKeys(state.BasePass, state.BaseRule, job.seq)
		stego := encode(job.payload, r, p, job.seq)
		sID := rand.Uint32()
		tot := uint32(math.Ceil(float64(len(stego)) / float64(ChunkSize)))

		tMu.RLock()
		target := tAddr
		tMu.RUnlock()
		if target == nil {
			continue
		}

		for i := uint32(0); i < tot; i++ {
			h := make([]byte, 13)
			h[0] = 4
			binary.BigEndian.PutUint32(h[1:5], sID)
			binary.BigEndian.PutUint32(h[5:9], tot)
			binary.BigEndian.PutUint32(h[9:13], i)
			start, end := i*ChunkSize, (i+1)*ChunkSize
			if end > uint32(len(stego)) {
				end = uint32(len(stego))
			}
			conn.WriteToUDP(append(h, stego[start:end]...), target)
		}
	}
}

func main() {
	lPort := flag.String("l", "9000", "Listen Port")
	tAddrStr := flag.String("t", "", "Peer IP:Port")
	pass := flag.String("p", "shibboleth", "Passphrase")
	rule := flag.Int("r", 912, "Wolfram Seed")
	tunIP := flag.String("ip", "10.0.0.1", "Local TUN IP")
	flag.Parse()

	state = &SessionState{BaseRule: *rule, BasePass: *pass}
	lAddr, _ := net.ResolveUDPAddr("udp", "0.0.0.0:"+*lPort)
	conn, _ = net.ListenUDP("udp", lAddr)
	if *tAddrStr != "" {
		tAddr, _ = net.ResolveUDPAddr("udp", *tAddrStr)
	}

	tunDevice, _ = water.New(water.Config{DeviceType: water.TUN})
	configureInterface(tunDevice.Name(), *tunIP)
	fmt.Printf("\033[35m[!] TURBO StegoVPN (BMP-LSB4) Online: %s\033[0m\n", *tunIP)

	for i := 0; i < runtime.NumCPU(); i++ {
		go worker()
	}

	// Receiver Loop
	go func() {
		numCores := runtime.NumCPU()
		for {
			buf := make([]byte, 2048)
			n, remote, err := conn.ReadFromUDP(buf)
			if err != nil || n < 1 {
				continue
			}
			tMu.Lock()
			tAddr = remote
			tMu.Unlock()

			if buf[0] == 1 {
				newSeq := binary.BigEndian.Uint32(buf[1:5])
				if newSeq > atomic.LoadUint32(&state.Seq) {
					atomic.StoreUint32(&state.Seq, newSeq)
				}
				continue
			}
			if n < 13 {
				continue
			}
			sID, tot, idx := binary.BigEndian.Uint32(buf[1:5]), binary.BigEndian.Uint32(buf[5:9]), binary.BigEndian.Uint32(buf[9:13])

			if full := frags.Add(sID, tot, idx, buf[13:n]); full != nil {
				go func(img []byte) {
					curr := atomic.LoadUint32(&state.Seq)
					// Fast Path
					r0, p0 := getKeys(state.BasePass, state.BaseRule, curr)
					if dec, seq, ok := decode(img, r0, p0); ok {
						atomic.StoreUint32(&state.Seq, seq+1)
						tunDevice.Write(dec)
						return
					}
					// Parallel Search
					resultChan := make(chan []byte, 1)
					var wg sync.WaitGroup
					found := int32(0)
					half := numCores / 2
					for i := -half; i <= half; i++ {
						if i == 0 {
							continue
						}
						wg.Add(1)
						go func(o int) {
							defer wg.Done()
							if atomic.LoadInt32(&found) == 1 {
								return
							}
							sSeq := uint32(int(curr) + o)
							r, p := getKeys(state.BasePass, state.BaseRule, sSeq)
							if dec, seq, ok := decode(img, r, p); ok {
								if atomic.CompareAndSwapInt32(&found, 0, 1) {
									if seq >= curr {
										atomic.StoreUint32(&state.Seq, seq+1)
									}
									resultChan <- dec
								}
							}
						}(i)
					}
					go func() { wg.Wait(); close(resultChan) }()
					if res, ok := <-resultChan; ok {
						tunDevice.Write(res)
					}
				}(full)
			}
		}
	}()

	// Read from TUN
	for {
		pkt := make([]byte, TUN_MTU)
		n, err := tunDevice.Read(pkt)
		if err != nil {
			break
		}
		s := atomic.AddUint32(&state.Seq, 1) - 1
		encryptChan <- encryptJob{payload: append([]byte(nil), pkt[:n]...), seq: s}
	}
}
