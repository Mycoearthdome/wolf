package main

import (
	"crypto/sha256"
	"encoding/binary"
	"flag"
	"fmt"
	"image"
	"image/color"
	"image/draw"
	_ "image/jpeg"
	"image/png"
	"math"
	"math/rand"
	"os"
)

const MagicSignature uint32 = 0xACE1FACE

type RGB struct{ R, G, B uint8 }

// --- CORE NKS & CRYPTO ---

func getRuleCode(ruleNum int) [7]uint8 {
	var code [7]uint8
	for i := 0; i < 7; i++ {
		code[i] = uint8(ruleNum % 3)
		ruleNum /= 3
	}
	return code
}

func generateDynamicRule(baseRule int, rowSum int, passwordHash []byte) int {
	mix := int(binary.BigEndian.Uint64(passwordHash[:8]))
	return (baseRule ^ (rowSum * 31) ^ mix) % 2187
}

func xorProcess(data []byte, password string) []byte {
	hash := sha256.Sum256([]byte(password))
	seed := int64(binary.BigEndian.Uint64(hash[:8]))
	rng := rand.New(rand.NewSource(seed))
	result := make([]byte, len(data))
	for i := range data {
		result[i] = data[i] ^ uint8(rng.Intn(256))
	}
	return result
}

// --- LAYER 1: INTERNAL NKS VAULT ---

func createInnerVault(rawData []byte, ruleNum int, password string) []byte {
	passHash := sha256.Sum256([]byte(password))
	payload := make([]byte, 8+len(rawData))
	binary.BigEndian.PutUint32(payload[0:4], MagicSignature)
	binary.BigEndian.PutUint32(payload[4:8], uint32(len(rawData)))
	copy(payload[8:], rawData)

	encrypted := xorProcess(payload, password)
	width := 1024
	pre, post := 64, 64
	dataRows := int(math.Ceil(float64(len(encrypted)*8) / float64(width*2)))
	height := pre + dataRows + post
	rowSize := (width + 3) &^ 3
	bmp := make([]byte, 54+(256*4)+(rowSize*height))

	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[2:6], uint32(len(bmp)))
	binary.LittleEndian.PutUint32(bmp[10:14], 54+(256*4))
	binary.LittleEndian.PutUint32(bmp[18:22], uint32(width))
	binary.LittleEndian.PutUint32(bmp[22:26], uint32(height))
	binary.LittleEndian.PutUint16(bmp[26:28], 1)
	binary.LittleEndian.PutUint16(bmp[28:30], 8)

	pRng := rand.New(rand.NewSource(int64(binary.BigEndian.Uint64(passHash[:8]))))
	for i := 0; i < 256; i++ {
		idx := 54 + i*4
		bmp[idx], bmp[idx+1], bmp[idx+2] = uint8(pRng.Intn(256)), uint8(pRng.Intn(256)), uint8(pRng.Intn(256))
	}

	grid := make([]uint8, width)
	grid[width/2] = 2
	pByte, pBit := 0, 0
	masterRng := rand.New(rand.NewSource(int64(binary.BigEndian.Uint64(passHash[8:16]))))

	for y := 0; y < height; y++ {
		rowSum := 0
		for _, v := range grid {
			rowSum += int(v)
		}
		ruleCode := getRuleCode(generateDynamicRule(ruleNum, rowSum, passHash[:]))
		rowSalt := masterRng.Int63()
		rowRng := rand.New(rand.NewSource(rowSalt))

		rowStart := 54 + (256 * 4) + (height-1-y)*rowSize
		nextGrid := make([]uint8, width)
		for x := 0; x < width; x++ {
			state := grid[x]
			pixelVal := uint8(rowRng.Intn(256))
			if y >= pre && pByte < len(encrypted) {
				bitShift := (int(state) + int(rowSalt) + x) % 3 * 2
				pixelVal = (pixelVal & ^(0x03 << bitShift)) | (((encrypted[pByte] >> pBit) & 0x03) << bitShift)
				pBit += 2
				if pBit == 8 {
					pBit, pByte = 0, pByte+1
				}
			}
			bmp[rowStart+x] = pixelVal
			l, r := grid[(x-1+width)%width], grid[(x+1)%width]
			nextGrid[x] = ruleCode[l+state+r]
		}
		grid = nextGrid
	}
	return bmp
}

// --- LAYER 2: CARRIER LSB ---

func doubleEncode(file, carrier, pass string, rule int) {
	raw, err := os.ReadFile(file)
	if err != nil {
		fmt.Println("File error:", err)
		return
	}
	vault := createInnerVault(raw, rule, pass)

	var cImg image.Image
	if carrier != "" {
		f, _ := os.Open(carrier)
		cImg, _, _ = image.Decode(f)
		f.Close()
	} else {
		cImg = image.NewRGBA(image.Rect(0, 0, 2048, 2048))
	}

	b := cImg.Bounds()
	stego := image.NewRGBA(b)
	draw.Draw(stego, b, cImg, b.Min, draw.Src)

	outPay := make([]byte, 4+len(vault))
	binary.BigEndian.PutUint32(outPay[:4], uint32(len(vault)))
	copy(outPay[4:], vault)

	pIdx, pBit := 0, 0
	for y := 0; y < b.Dy() && pIdx < len(outPay); y++ {
		for x := 0; x < b.Dx() && pIdx < len(outPay); x++ {
			px := stego.RGBAAt(x, y)
			chans := []*uint8{&px.R, &px.G, &px.B}
			for _, val := range chans {
				if pIdx < len(outPay) {
					*val = (*val & 0xFC) | ((outPay[pIdx] >> pBit) & 0x03)
					pBit += 2
					if pBit == 8 {
						pBit, pIdx = 0, pIdx+1
					}
				}
			}
			stego.SetRGBA(x, y, px)
		}
	}
	f, _ := os.Create("final_stego.png")
	png.Encode(f, stego)
	fmt.Println("Double-Hardened Stego created: final_stego.png")
}

func doubleDecode(stegoFile, pass string, rule int) {
	fIn, err := os.Open(stegoFile)
	if err != nil {
		fmt.Println("Error:", err)
		return
	}
	img, err := png.Decode(fIn)
	fIn.Close()
	if err != nil {
		fmt.Println("Error:", err)
		return
	}

	b := img.Bounds()
	var rawVault []byte
	var curB uint8
	bCount, vSize, found := 0, uint32(0), false

	for y := 0; y < b.Dy(); y++ {
		for x := 0; x < b.Dx(); x++ {
			c := color.NRGBAModel.Convert(img.At(x, y)).(color.NRGBA)
			for _, val := range []uint8{c.R, c.G, c.B} {
				curB |= (val & 0x03) << bCount
				bCount += 2
				if bCount == 8 {
					rawVault = append(rawVault, curB)
					curB, bCount = 0, 0
					if !found && len(rawVault) == 4 {
						vSize = binary.BigEndian.Uint32(rawVault)
						found = true
					}
					if found && uint32(len(rawVault)) == vSize+4 {
						goto InnerVault
					}
				}
			}
		}
	}

InnerVault:
	iv := rawVault[4:]
	w := int(binary.LittleEndian.Uint32(iv[18:22]))
	h := int(binary.LittleEndian.Uint32(iv[22:26]))
	off := int(binary.LittleEndian.Uint32(iv[10:14]))
	rowSize := (w + 3) &^ 3

	passHash := sha256.Sum256([]byte(pass))
	grid := make([]uint8, w)
	grid[w/2] = 2
	masterRng := rand.New(rand.NewSource(int64(binary.BigEndian.Uint64(passHash[8:16]))))

	var extracted []byte
	var tmpB uint8
	tmpBit := 0

	for y := 0; y < h; y++ {
		rowSum := 0
		for _, v := range grid {
			rowSum += int(v)
		}
		ruleCode := getRuleCode(generateDynamicRule(rule, rowSum, passHash[:]))
		rowSalt := masterRng.Int63()
		rowStart := off + (h-1-y)*rowSize

		nextGrid := make([]uint8, w)
		for x := 0; x < w; x++ {
			state := grid[x]
			if y >= 64 && rowStart+x < len(iv) {
				shift := (int(state) + int(rowSalt) + x) % 3 * 2
				bits := (iv[rowStart+x] >> shift) & 0x03
				tmpB |= (bits << tmpBit)
				tmpBit += 2
				if tmpBit == 8 {
					extracted = append(extracted, tmpB)
					tmpB, tmpBit = 0, 0
				}
			}
			l, r := grid[(x-1+w)%w], grid[(x+1)%w]
			nextGrid[x] = ruleCode[l+state+r]
		}
		grid = nextGrid
	}

	final := xorProcess(extracted, pass)
	if len(final) >= 8 && binary.BigEndian.Uint32(final[:4]) == MagicSignature {
		size := binary.BigEndian.Uint32(final[4:8])
		if int(size)+8 > len(final) {
			fmt.Println("ACCESS DENIED: Logic Desync Detected.")
			return
		}
		os.WriteFile("recovered.bin", final[8:8+size], 0644)
		fmt.Println("UNLOCKED: written recovered.bin successfully.")
	} else {
		fmt.Println("ACCESS DENIED: Wrong password or rule.")
	}
}

func main() {
	m := flag.String("m", "encode", "")
	f := flag.String("f", "", "")
	c := flag.String("carrier", "", "")
	r := flag.Int("rule", 912, "")
	p := flag.String("pass", "wolfram", "")
	flag.Parse()
	if *m == "encode" {
		doubleEncode(*f, *c, *p, *r)
	} else {
		doubleDecode(*f, *p, *r)
	}
}
