package main

import (
	"crypto/sha256"
	"encoding/binary"
	"flag"
	"fmt"
	"math"
	"os"
	"runtime"
	"strings"
	"sync"
)

func getChecksum(data []byte) string {
	h := sha256.New()
	h.Write(data)
	return fmt.Sprintf("%x", h.Sum(nil))
}

func drawProgress(current, total int, label string) {
	if total <= 0 {
		return
	}
	const barWidth = 30
	percent := float64(current) / float64(total)
	filled := int(percent * barWidth)
	bar := strings.Repeat("█", filled) + strings.Repeat("-", barWidth-filled)
	fmt.Printf("\r%s: [%s] %3.0f%%", label, bar, percent*100)
	if current == total {
		fmt.Println()
	}
}

func applyRule(l, m, r uint8, rule uint8) uint8 {
	var result uint8
	for i := 0; i < 8; i++ {
		bitL, bitM, bitR := (l>>i)&1, (m>>i)&1, (r>>i)&1
		index := (bitL << 2) | (bitM << 1) | bitR
		if (rule & (1 << index)) != 0 {
			result |= (1 << i)
		}
	}
	return result
}

func evolveParallel(grid [][]uint8, width, height int, rule uint8) {
	numCPUs := runtime.NumCPU()
	chunkSize := width / numCPUs
	for y := 1; y < height; y++ {
		if y%500 == 0 {
			drawProgress(y, height, "Evolving Grid")
		}
		var wg sync.WaitGroup
		for i := 0; i < numCPUs; i++ {
			wg.Add(1)
			start, end := i*chunkSize, (i+1)*chunkSize
			if i == numCPUs-1 {
				end = width
			}
			go func(y, s, e int) {
				defer wg.Done()
				for x := s; x < e; x++ {
					l, m, r := grid[y-1][(x-1+width)%width], grid[y-1][x], grid[y-1][(x+1)%width]
					grid[y][x] = applyRule(l, m, r, rule)
				}
			}(y, start, end)
		}
		wg.Wait()
	}
	drawProgress(height, height, "Evolving Grid")
}

func main() {
	mode := flag.String("m", "encode", "Mode")
	filePath := flag.String("f", "", "File")
	preIter := flag.Int("pre", 2026, "Pre-steps")
	ruleNum := flag.Int("rule", 73, "Rule")
	flag.Parse()

	if *mode == "encode" {
		encode(*filePath, *preIter, uint8(*ruleNum))
	} else {
		decode(*filePath, *preIter, uint8(*ruleNum))
	}
}

func encode(path string, pre int, rule uint8) {
	rawData, _ := os.ReadFile(path)
	fileSize := uint32(len(rawData))

	// Added a more generous buffer (+100 rows) to prevent edge-of-square panics
	totalBytesNeeded := float64(fileSize) + 4.0 + (float64(pre+100) * 8192.0 * 3.0)
	side := int(math.Ceil(math.Sqrt(totalBytesNeeded / 3.0)))
	if side < 128 {
		side = 128
	}

	width, height := side, side
	rowSize := (width*3 + 3) &^ 3

	grid := make([][]uint8, height)
	for i := range grid {
		grid[i] = make([]uint8, width)
	}
	grid[0][width/2] = 0xFF
	evolveParallel(grid, width, height, rule)

	fileHeaderSize := 14 + 40
	bmpData := make([]byte, fileHeaderSize+(rowSize*height))

	copy(bmpData[0:2], "BM")
	binary.LittleEndian.PutUint32(bmpData[2:6], uint32(len(bmpData)))
	binary.LittleEndian.PutUint32(bmpData[10:14], uint32(fileHeaderSize))
	binary.LittleEndian.PutUint32(bmpData[14:18], 40)
	binary.LittleEndian.PutUint32(bmpData[18:22], uint32(width))
	binary.LittleEndian.PutUint32(bmpData[22:26], uint32(height))
	binary.LittleEndian.PutUint16(bmpData[26:28], 1)
	binary.LittleEndian.PutUint16(bmpData[28:30], 24)

	payload := make([]byte, 4+fileSize)
	binary.BigEndian.PutUint32(payload[:4], fileSize)
	copy(payload[4:], rawData)

	pIdx := 0
	for y := 0; y < height; y++ {
		rowStart := fileHeaderSize + (height-1-y)*rowSize
		for x := 0; x < width; x++ {
			val := grid[y][x]
			b, g, r := val, val, val
			if y >= pre && pIdx < len(payload) {
				b ^= payload[pIdx]
				pIdx++
				if pIdx < len(payload) {
					g ^= payload[pIdx]
					pIdx++
				}
				if pIdx < len(payload) {
					r ^= payload[pIdx]
					pIdx++
				}
			}
			bmpData[rowStart+x*3] = b
			bmpData[rowStart+x*3+1] = g
			bmpData[rowStart+x*3+2] = r
		}
	}

	os.WriteFile("encoded_wolfram.bmp", bmpData, 0644)
	fmt.Printf("Square: %dx%d | Encoded SHA256: %s\n", width, height, getChecksum(rawData))
}

func decode(path string, pre int, rule uint8) {
	data, _ := os.ReadFile(path)
	width := int(binary.LittleEndian.Uint32(data[18:22]))
	height := int(binary.LittleEndian.Uint32(data[22:26]))
	fileHeaderSize := int(binary.LittleEndian.Uint32(data[10:14]))
	rowSize := (width*3 + 3) &^ 3

	grid := make([][]uint8, height)
	for i := range grid {
		grid[i] = make([]uint8, width)
	}
	grid[0][width/2] = 0xFF
	evolveParallel(grid, width, height, rule)

	// Use uint64 for pIdx to prevent overflow on massive files
	var pIdx uint64 = 0
	getByte := func() uint8 {
		y := pre + int(pIdx/uint64(width*3))

		// Hard safety: if we hit the end of the image, return 0 instead of panicking
		if y >= height {
			return 0
		}

		x := int((pIdx / 3) % uint64(width))
		c := int(pIdx % 3)
		pIdx++

		rowStart := fileHeaderSize + (height-1-y)*rowSize
		return data[rowStart+x*3+c] ^ grid[y][x]
	}

	sizeBuf := make([]byte, 4)
	for i := 0; i < 4; i++ {
		sizeBuf[i] = getByte()
	}
	fileSize := binary.BigEndian.Uint32(sizeBuf)

	recovered := make([]byte, fileSize)
	for i := uint32(0); i < fileSize; i++ {
		if i%1000000 == 0 {
			drawProgress(int(i), int(fileSize), "Extracting")
		}
		recovered[i] = getByte()
	}
	drawProgress(int(fileSize), int(fileSize), "Extracting")

	os.WriteFile("decoded_output.bin", recovered, 0644)
	fmt.Printf("Decoded SHA256: %s\n", getChecksum(recovered))
}
