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
	"os"
	"sync"
	"time"
)

const (
	MagicSignature uint32 = 0xACE1FACE
	ChunkSize             = 3500
	ColorReset            = "\033[0m"
	ColorCyan             = "\033[36m"
)

type SessionState struct {
	mu       sync.Mutex
	BaseRule int
	BasePass string
	Seq      uint32
}

var (
	state *SessionState
	conn  *net.UDPConn
	tAddr *net.UDPAddr
	frags = &FragMan{Sess: make(map[uint32]*FileSess)}
	acks  = make(map[uint32]chan bool)
	aMu   sync.Mutex
)

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

// --- Steganography & Crypto Core ---

func compress(data []byte) []byte {
	var b bytes.Buffer
	w := gzip.NewWriter(&b)
	w.Write(data)
	w.Close()
	return b.Bytes()
}

func decompress(data []byte) ([]byte, error) {
	r, err := gzip.NewReader(bytes.NewReader(data))
	if err != nil {
		return nil, err
	}
	defer r.Close()
	return io.ReadAll(r)
}

func (s *SessionState) GetKey(seq uint32) (int, string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	h := sha256.Sum256([]byte(fmt.Sprintf("%s-%d", s.BasePass, seq)))
	return (s.BaseRule + int(seq)) % 2187, fmt.Sprintf("%x", h)
}

func getRuleCode(n int) [27]uint8 {
	var c [27]uint8
	for i := 0; i < 27; i++ {
		c[i] = uint8(n % 3)
		n /= 3
	}
	return c
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
	h := sha256.Sum256([]byte(p))
	comp := compress(raw)
	pay := make([]byte, 8+len(comp))
	binary.BigEndian.PutUint32(pay[:4], MagicSignature)
	binary.BigEndian.PutUint32(pay[4:8], uint32(len(comp)))
	copy(pay[8:], comp)
	enc := xor(pay, p)
	w, ht := 256, 16+int(math.Ceil(float64(len(enc)*8)/512.0))+16
	rowS := (w + 3) &^ 3
	bmp := make([]byte, 54+1024+(rowS*ht))
	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[10:14], 1078)
	binary.LittleEndian.PutUint32(bmp[18:22], uint32(w))
	binary.LittleEndian.PutUint32(bmp[22:26], uint32(ht))
	binary.LittleEndian.PutUint16(bmp[28:30], 8)
	grid := make([]uint8, w)
	grid[w/2] = 2
	pB, pBit, mRng := 0, 0, rand.New(rand.NewSource(int64(binary.BigEndian.Uint64(h[8:16]))))
	for y := 0; y < ht; y++ {
		rSum := 0
		for _, v := range grid {
			rSum += int(v)
		}
		rCode := getRuleCode((r ^ (rSum * 31)) % 2187)
		salt := mRng.Int63()
		rRng, off := rand.New(rand.NewSource(salt)), 1078+(ht-1-y)*rowS
		next := make([]uint8, w)
		for x := 0; x < w; x++ {
			if y >= 16 && pB < len(enc) {
				sh := (int(grid[x]%3) + int(salt) + x) % 3 * 2
				bmp[off+x] = (uint8(rRng.Intn(256)) & ^(0x03 << sh)) | (((enc[pB] >> pBit) & 0x03) << sh)
				pBit += 2
				if pBit == 8 {
					pBit, pB = 0, pB+1
				}
			} else {
				bmp[off+x] = uint8(rRng.Intn(256))
			}
			l, rv := grid[(x-1+w)%w]%3, grid[(x+1)%w]%3
			next[x] = rCode[int(l)*9+int(grid[x]%3)*3+int(rv)]
		}
		grid = next
	}
	return bmp
}

func encode(msg []byte, r int, p string, seq uint32) []byte {
	vault := createVault(msg, r, p)
	side := int(math.Ceil(math.Sqrt(float64((8+len(vault))*8) / 6.0)))
	if side < 512 {
		side = 512
	}
	img := image.NewNRGBA(image.Rect(0, 0, side, side))
	pay := make([]byte, 8+len(vault))
	binary.BigEndian.PutUint32(pay[:4], uint32(len(vault)))
	binary.BigEndian.PutUint32(pay[4:8], seq)
	copy(pay[8:], vault)
	idx, bit := 0, 0
	for i := 0; i < len(img.Pix) && idx < len(pay); i++ {
		if (i+1)%4 == 0 {
			continue
		}
		img.Pix[i] = (img.Pix[i] & 0xFC) | ((pay[idx] >> bit) & 0x03)
		bit += 2
		if bit == 8 {
			bit, idx = 0, idx+1
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
	var raw []byte
	var cur uint8
	bit, vS, seq, ok := 0, uint32(0), uint32(0), false
	for i := 0; i < len(nrgba.Pix); i++ {
		if (i+1)%4 == 0 {
			continue
		}
		cur |= (nrgba.Pix[i] & 0x03) << bit
		bit += 2
		if bit == 8 {
			raw = append(raw, cur)
			cur, bit = 0, 0
			if !ok && len(raw) >= 8 {
				vS, seq, ok = binary.BigEndian.Uint32(raw[:4]), binary.BigEndian.Uint32(raw[4:8]), true
			}
			if ok && uint32(len(raw)) >= vS+8 {
				break
			}
		}
	}
	if !ok || uint32(len(raw)) < vS+8 {
		return nil, 0, false
	}
	iv, h := raw[8:vS+8], sha256.Sum256([]byte(p))
	w, ht := int(binary.LittleEndian.Uint32(iv[18:22])), int(binary.LittleEndian.Uint32(iv[22:26]))
	off, rowS, grid := 1078, (w+3)&^3, make([]uint8, w)
	grid[w/2] = 2
	mRng := rand.New(rand.NewSource(int64(binary.BigEndian.Uint64(h[8:16]))))
	var ext []byte
	var tB uint8
	tBit := 0
	for y := 0; y < ht; y++ {
		rSum := 0
		for _, v := range grid {
			rSum += int(v)
		}
		rCode := getRuleCode((r ^ (rSum * 31)) % 2187)
		salt := mRng.Int63()
		rOff := off + (ht-1-y)*rowS
		next := make([]uint8, w)
		for x := 0; x < w; x++ {
			if y >= 16 && rOff+x < len(iv) {
				sh := (int(grid[x]%3) + int(salt) + x) % 3 * 2
				tB |= ((iv[rOff+x] >> sh) & 0x03) << tBit
				tBit += 2
				if tBit == 8 {
					ext = append(ext, tB)
					tB, tBit = 0, 0
				}
			}
			l, rv := grid[(x-1+w)%w]%3, grid[(x+1)%w]%3
			next[x] = rCode[int(l)*9+int(grid[x]%3)*3+int(rv)]
		}
		grid = next
	}
	f := xor(ext, p)
	if len(f) >= 8 && binary.BigEndian.Uint32(f[:4]) == MagicSignature {
		sz := binary.BigEndian.Uint32(f[4:8])
		dec, err := decompress(f[8 : 8+sz])
		if err == nil {
			return dec, seq, true
		}
	}
	return nil, 0, false
}

func (f *FragMan) Add(sID, tot, idx uint32, d []byte) []byte {
	f.mu.Lock()
	defer f.mu.Unlock()
	if _, ok := f.Sess[sID]; !ok {
		f.Sess[sID] = &FileSess{Data: make([][]byte, tot), Total: int(tot)}
	}
	fs := f.Sess[sID]
	fs.mu.Lock()
	defer fs.mu.Unlock()
	if fs.Data[idx] == nil {
		fs.Data[idx] = d
		fs.Received++
	}
	if fs.Received == fs.Total {
		res := bytes.Join(fs.Data, nil)
		delete(f.Sess, sID)
		return res
	}
	return nil
}

// --- Main Runner ---

func main() {
	lPort := flag.String("l", "9000", "Listen Port")
	tAddrStr := flag.String("t", "127.0.0.1:9001", "Target IP:Port")
	pass := flag.String("p", "wolfram123", "Passphrase")
	rule := flag.Int("r", 912, "Wolfram Seed")
	flag.Parse()

	state = &SessionState{BaseRule: *rule, BasePass: *pass, Seq: 0}
	lAddr, _ := net.ResolveUDPAddr("udp", "0.0.0.0:"+*lPort)
	conn, _ = net.ListenUDP("udp", lAddr)
	tAddr, _ = net.ResolveUDPAddr("udp", *tAddrStr)

	fmt.Fprintf(os.Stderr, "%s[STEGO-TUNNEL] Running. L:%s -> T:%s%s\n", ColorCyan, *lPort, *tAddrStr, ColorReset)

	go func() {
		for {
			buf := make([]byte, 65535)
			n, _, _ := conn.ReadFromUDP(buf)
			if n < 13 {
				continue
			}
			pType, sID, tot, idx := buf[0], binary.BigEndian.Uint32(buf[1:5]), binary.BigEndian.Uint32(buf[5:9]), binary.BigEndian.Uint32(buf[9:13])
			full := frags.Add(sID, tot, idx, buf[13:n])
			if full != nil {
				state.mu.Lock()
				curS := state.Seq
				state.mu.Unlock()
				var payload []byte
				var seq uint32
				var ok bool
				for i := -10; i <= 20; i++ {
					r, p := state.GetKey(uint32(int(curS) + i))
					payload, seq, ok = decode(full, r, p)
					if ok {
						break
					}
				}
				if ok {
					switch pType {
					case 4: // Data
						os.Stdout.Write(payload)
						dispatch(seq, 2, []byte("ACK"))
					case 2: // ACK
						aMu.Lock()
						if ch, ok := acks[seq]; ok {
							select {
							case ch <- true:
							default:
							}
						}
						aMu.Unlock()
					}
					if seq >= curS {
						state.mu.Lock()
						state.Seq = seq + 1
						state.mu.Unlock()
					}
				}
			}
		}
	}()

	b := make([]byte, 2048)
	for {
		n, err := os.Stdin.Read(b)
		if n > 0 {
			dispatch(0, 4, b[:n])
		}
		if err != nil {
			break
		}
	}
}

func dispatch(targetSeq uint32, pType byte, payload []byte) {
	var seq uint32
	// Tagged switch logic for sequence handling
	switch pType {
	case 2: // ACK: Uses the sequence of the packet being acknowledged
		seq = targetSeq
	case 4: // Data: Increments the global session sequence
		state.mu.Lock()
		seq = state.Seq
		state.Seq++
		state.mu.Unlock()
	}

	r, p := state.GetKey(seq)
	stego := encode(payload, r, p, seq)
	sID := rand.Uint32()
	tot := uint32(math.Ceil(float64(len(stego)) / float64(ChunkSize)))

	if pType == 2 { // Fire-and-forget for ACKs
		transmit(pType, sID, tot, stego)
		return
	}

	// Reliable delivery for Data
	ch := make(chan bool, 1)
	aMu.Lock()
	acks[seq] = ch
	aMu.Unlock()

	for retry := 0; retry < 3; retry++ {
		transmit(pType, sID, tot, stego)
		select {
		case <-ch:
			return
		case <-time.After(3 * time.Second):
		}
	}
}

func transmit(pType byte, sID, tot uint32, stego []byte) {
	for i := uint32(0); i < tot; i++ {
		h := make([]byte, 13)
		h[0] = pType
		binary.BigEndian.PutUint32(h[1:5], sID)
		binary.BigEndian.PutUint32(h[5:9], tot)
		binary.BigEndian.PutUint32(h[9:13], i)
		start, end := i*ChunkSize, (i+1)*ChunkSize
		if end > uint32(len(stego)) {
			end = uint32(len(stego))
		}
		conn.WriteToUDP(append(h, stego[start:end]...), tAddr)
		time.Sleep(time.Millisecond)
	}
}
