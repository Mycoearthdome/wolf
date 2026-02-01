package main

import (
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"encoding/binary"
	"flag"
	"fmt"
	"image"
	"image/draw"
	_ "image/jpeg"
	"image/png"
	"io"
	"math"
	"math/rand"
	"net"
	"os/exec"
	"runtime"
	"sync"
	"sync/atomic"
	"time"

	"github.com/songgao/water"
)

const (
	MagicSignature uint32 = 0xACE1FACE
	ChunkSize             = 1200
	TUN_MTU               = 400
	VaultWidth            = 256
	VaultHeight           = 128
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

// --- Optimized Stego Logic ---

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
	enc := xor(payload, p)

	rowS := (VaultWidth + 3) &^ 3
	bmp := make([]byte, 54+1024+(rowS*VaultHeight))
	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[18:22], uint32(VaultWidth))
	binary.LittleEndian.PutUint32(bmp[22:26], uint32(VaultHeight))
	binary.LittleEndian.PutUint16(bmp[28:30], 8)

	grid := make([]uint8, VaultWidth)
	grid[VaultWidth/2] = 2
	h := sha256.Sum256([]byte(p))
	mRng := rand.New(rand.NewSource(int64(binary.BigEndian.Uint64(h[8:16]))))

	for y := 0; y < VaultHeight; y++ {
		rSum := 0
		for _, v := range grid {
			rSum += int(v)
		}
		rCode := [27]uint8{}
		n := (r ^ (rSum * 31)) % 2187
		if n < 0 {
			n = -n
		}
		for i := 0; i < 27; i++ {
			rCode[i] = uint8(n % 3)
			n /= 3
		}

		salt := mRng.Int63()
		rRng := rand.New(rand.NewSource(salt))
		off := 1078 + (VaultHeight-1-y)*rowS
		next := make([]uint8, VaultWidth)

		for x := 0; x < VaultWidth; x++ {
			if y >= 16 && y < 112 {
				byteIdx := (y-16)*64 + (x / 4)
				if byteIdx < len(enc) {
					sh := (int(grid[x]%3) + int(salt) + x) % 3 * 2
					bmp[off+x] = (uint8(rRng.Intn(256)) & ^(0x03 << sh)) | (((enc[byteIdx] >> (uint(x%4) * 2)) & 0x03) << sh)
				} else {
					bmp[off+x] = uint8(rRng.Intn(256))
				}
			} else {
				bmp[off+x] = uint8(rRng.Intn(256))
			}
			l, rv := grid[(x-1+VaultWidth)%VaultWidth]%3, grid[(x+1)%VaultWidth]%3
			next[x] = rCode[int(l)*9+int(grid[x]%3)*3+int(rv)]
		}
		grid = next
	}
	return bmp
}

func encode(msg []byte, r int, p string, seq uint32) []byte {
	vault := createVault(msg, r, p)
	img := image.NewNRGBA(image.Rect(0, 0, 256, 256))
	rand.New(rand.NewSource(int64(seq))).Read(img.Pix)

	header := binary.BigEndian.AppendUint32(binary.BigEndian.AppendUint32(nil, uint32(len(vault))), seq)
	data := append(header, vault...)

	dIdx, bShift := 0, uint(0)
	for i := 0; i < len(img.Pix) && dIdx < len(data); i++ {
		if (i+1)%4 == 0 {
			continue
		}
		img.Pix[i] = (img.Pix[i] & 0xFC) | ((data[dIdx] >> bShift) & 0x03)
		bShift += 2
		if bShift == 8 {
			bShift, dIdx = 0, dIdx+1
		}
	}
	buf := new(bytes.Buffer)
	png.Encode(buf, img)
	return buf.Bytes()
}

func decode(stego []byte, r int, p string) ([]byte, uint32, bool) {
	img, err := png.Decode(bytes.NewReader(stego))
	if err != nil {
		return nil, 0, false
	}
	b := img.Bounds()
	nrgba := image.NewNRGBA(b)
	draw.Draw(nrgba, b, img, b.Min, draw.Src)

	var hdr [8]byte
	idx, bit := 0, uint(0)
	for i := 0; i < len(nrgba.Pix) && idx < 8; i++ {
		if (i+1)%4 == 0 {
			continue
		}
		hdr[idx] |= (nrgba.Pix[i] & 0x03) << bit
		bit += 2
		if bit == 8 {
			bit, idx = 0, idx+1
		}
	}
	vS := binary.BigEndian.Uint32(hdr[:4])
	seq := binary.BigEndian.Uint32(hdr[4:8])
	if vS > 1000000 || vS < 1078 {
		return nil, 0, false
	}

	vault := make([]byte, vS)
	vIdx, vBit, skipped := 0, uint(0), 0
	for i := 0; i < len(nrgba.Pix) && vIdx < int(vS); i++ {
		if (i+1)%4 == 0 {
			continue
		}
		if skipped < 32 {
			skipped++
			continue
		}
		vault[vIdx] |= (nrgba.Pix[i] & 0x03) << vBit
		vBit += 2
		if vBit == 8 {
			vBit, vIdx = 0, vIdx+1
		}
	}

	rowS := (VaultWidth + 3) &^ 3
	grid := make([]uint8, VaultWidth)
	grid[VaultWidth/2] = 2
	h := sha256.Sum256([]byte(p))
	mRng := rand.New(rand.NewSource(int64(binary.BigEndian.Uint64(h[8:16]))))

	var encData []byte
	var tB uint8
	var tBit uint = 0
	for y := 0; y < VaultHeight; y++ {
		rSum := 0
		for _, v := range grid {
			rSum += int(v)
		}
		rCode := [27]uint8{}
		n := (r ^ (rSum * 31)) % 2187
		if n < 0 {
			n = -n
		}
		for i := 0; i < 27; i++ {
			rCode[i] = uint8(n % 3)
			n /= 3
		}
		salt := mRng.Int63()
		off := 1078 + (VaultHeight-1-y)*rowS
		next := make([]uint8, VaultWidth)
		for x := 0; x < VaultWidth; x++ {
			if y >= 16 && y < 112 {
				sh := (int(grid[x]%3) + int(salt) + x) % 3 * 2
				tB |= ((vault[off+x] >> sh) & 0x03) << tBit
				tBit += 2
				if tBit == 8 {
					encData = append(encData, tB)
					tB, tBit = 0, 0
				}
			}
			l, rv := grid[(x-1+VaultWidth)%VaultWidth]%3, grid[(x+1)%VaultWidth]%3
			next[x] = rCode[int(l)*9+int(grid[x]%3)*3+int(rv)]
		}
		grid = next
	}

	f := xor(encData, p)
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

// --- Networking & Management ---

func configureInterface(name, localIP string) {
	if runtime.GOOS != "linux" {
		return
	}
	_ = exec.Command("ip", "link", "set", "dev", name, "up", "mtu", fmt.Sprintf("%d", TUN_MTU)).Run()
	_ = exec.Command("ip", "addr", "add", localIP+"/24", "dev", name).Run()
}

func worker() {
	for job := range encryptChan {
		r, p := getKeys(state.BasePass, state.BaseRule, job.seq)
		stego := encode(job.payload, r, p, job.seq)
		sID, tot := rand.Uint32(), uint32(math.Ceil(float64(len(stego))/float64(ChunkSize)))
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
	fmt.Printf("\033[32m[+] Ultra-Fast StegoVPN: %s (Cores: %d)\033[0m\n", *tunIP, runtime.NumCPU())

	for i := 0; i < runtime.NumCPU(); i++ {
		go worker()
	}

	go func() {
		for {
			time.Sleep(3 * time.Second)
			tMu.RLock()
			target := tAddr
			tMu.RUnlock()
			if target != nil {
				h := make([]byte, 13)
				h[0] = 1
				binary.BigEndian.PutUint32(h[1:5], atomic.LoadUint32(&state.Seq))
				conn.WriteToUDP(h, target)
			}
		}
	}()

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
				go func(imgData []byte) {
					curr := atomic.LoadUint32(&state.Seq)
					// Fast Path
					r0, p0 := getKeys(state.BasePass, state.BaseRule, curr)
					if dec, seq, ok := decode(imgData, r0, p0); ok {
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
						go func(offset int) {
							defer wg.Done()
							if atomic.LoadInt32(&found) == 1 {
								return
							}
							sSeq := uint32(int(curr) + offset)
							r, p := getKeys(state.BasePass, state.BaseRule, sSeq)
							if dec, seq, ok := decode(imgData, r, p); ok {
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
