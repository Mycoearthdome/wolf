package main

import (
	"encoding/binary"
	"flag"
	"fmt"
	"math"
	"math/rand"
	"os"
	"strconv"
	"strings"
	"time"
)

type RGB struct {
	R, G, B uint8
}

func parseColor(s string) RGB {
	parts := strings.Split(s, ",")
	if len(parts) != 3 {
		return RGB{0, 0, 0}
	}
	r, _ := strconv.Atoi(parts[0])
	g, _ := strconv.Atoi(parts[1])
	b, _ := strconv.Atoi(parts[2])
	return RGB{uint8(r), uint8(g), uint8(b)}
}

func (c RGB) String() string {
	return fmt.Sprintf("%d,%d,%d", c.R, c.G, c.B)
}

// --- NKS k=3 Totalistic Engine ---

func getRuleCode(ruleNum int) [7]uint8 {
	var code [7]uint8
	for i := 0; i < 7; i++ {
		code[i] = uint8(ruleNum % 3)
		ruleNum /= 3
	}
	return code
}

func applyTotalisticRule(l, m, r uint8, ruleCode [7]uint8) uint8 {
	return ruleCode[l+m+r]
}

// --- Steganography Core ---

func encode(path string, pre, post, ruleNum, width int, palette [3]RGB) {
	rawData, err := os.ReadFile(path)
	if err != nil {
		fmt.Println("Error reading file:", err)
		return
	}

	fileSize := uint32(len(rawData))
	payload := make([]byte, 4+fileSize)
	binary.BigEndian.PutUint32(payload[:4], fileSize)
	copy(payload[4:], rawData)

	ruleCode := getRuleCode(ruleNum)
	totalBits := len(payload) * 8
	pixelsNeeded := int(math.Ceil(float64(totalBits) / 3.0))

	dataRows := int(math.Ceil(float64(pixelsNeeded) / float64(width)))
	height := pre + dataRows + post
	rowSize := (width*3 + 3) &^ 3
	fileSizeTotal := 54 + (rowSize * height)

	grid := make([][]uint8, height)
	for i := range grid {
		grid[i] = make([]uint8, width)
	}
	grid[0][width/2] = 2 // Central Seed

	for y := 1; y < height; y++ {
		for x := 0; x < width; x++ {
			l := grid[y-1][(x-1+width)%width]
			m := grid[y-1][x]
			r := grid[y-1][(x+1)%width]
			grid[y][x] = applyTotalisticRule(l, m, r, ruleCode)
		}
	}

	bmp := make([]byte, fileSizeTotal)
	copy(bmp[0:2], "BM")
	binary.LittleEndian.PutUint32(bmp[2:6], uint32(fileSizeTotal))
	binary.LittleEndian.PutUint32(bmp[10:14], 54)
	binary.LittleEndian.PutUint32(bmp[14:18], 40)
	binary.LittleEndian.PutUint32(bmp[18:22], uint32(width))
	binary.LittleEndian.PutUint32(bmp[22:26], uint32(height))
	binary.LittleEndian.PutUint16(bmp[26:28], 1)
	binary.LittleEndian.PutUint16(bmp[28:30], 24)

	pByte, pBit := 0, 0
	for y := 0; y < height; y++ {
		rowStart := 54 + (height-1-y)*rowSize
		for x := 0; x < width; x++ {
			color := palette[grid[y][x]]
			channels := []uint8{color.B, color.G, color.R}

			if y >= pre && pByte < len(payload) {
				for i := 0; i < 3 && pByte < len(payload); i++ {
					bit := (payload[pByte] >> pBit) & 1
					channels[i] = (channels[i] & 0xFE) | bit
					pBit++
					if pBit == 8 {
						pBit = 0
						pByte++
					}
				}
			}
			bmp[rowStart+x*3], bmp[rowStart+x*3+1], bmp[rowStart+x*3+2] = channels[0], channels[1], channels[2]
		}
	}

	outputName := "nks_stego.bmp"
	os.WriteFile(outputName, bmp, 0644)

	// --- CRITICAL OUTPUT FOR THE USER ---
	fmt.Println("\n==========================================================")
	fmt.Println("    NKS STEGANOGRAPHY ENCODING COMPLETE")
	fmt.Println("==========================================================")
	fmt.Printf("Output File: %s\n", outputName)
	fmt.Printf("Dimensions:  %d x %d\n", width, height)
	fmt.Printf("Rule Used:   %d\n", ruleNum)
	fmt.Printf("Palette:     c0:%s | c1:%s | c2:%s\n", palette[0], palette[1], palette[2])
	fmt.Println("----------------------------------------------------------")
	fmt.Println("To decode this file later, use the following command:")
	fmt.Printf("./wolf -m decode -f %s -rule %d -pre %d -c0 %s -c1 %s -c2 %s\n",
		outputName, ruleNum, pre, palette[0], palette[1], palette[2])
	fmt.Println("==========================================================\n")
}

func decode(path string, pre, ruleNum int, palette [3]RGB) {
	data, err := os.ReadFile(path)
	if err != nil {
		fmt.Println("Error reading BMP:", err)
		return
	}

	width := int(binary.LittleEndian.Uint32(data[18:22]))
	height := int(binary.LittleEndian.Uint32(data[22:26]))
	rowSize := (width*3 + 3) &^ 3
	ruleCode := getRuleCode(ruleNum)

	grid := make([][]uint8, height)
	for i := range grid {
		grid[i] = make([]uint8, width)
	}
	grid[0][width/2] = 2
	for y := 1; y < height; y++ {
		for x := 0; x < width; x++ {
			l := grid[y-1][(x-1+width)%width]
			m := grid[y-1][x]
			r := grid[y-1][(x+1)%width]
			grid[y][x] = applyTotalisticRule(l, m, r, ruleCode)
		}
	}

	var payload []byte
	var currentByte uint8
	bitCount, foundSize := 0, false
	var fileSize uint32

	for y := pre; y < height; y++ {
		rowStart := 54 + (height-1-y)*rowSize
		for x := 0; x < width; x++ {
			for c := 0; c < 3; c++ {
				bit := data[rowStart+x*3+c] & 1
				currentByte |= (bit << bitCount)
				bitCount++
				if bitCount == 8 {
					payload = append(payload, currentByte)
					currentByte, bitCount = 0, 0
					if !foundSize && len(payload) == 4 {
						fileSize = binary.BigEndian.Uint32(payload)
						foundSize = true
					}
					if foundSize && len(payload) == int(fileSize)+4 {
						os.WriteFile("extracted_data.bin", payload[4:], 0644)
						fmt.Println("Success: Data extracted to 'extracted_data.bin'")
						return
					}
				}
			}
		}
	}
}

func main() {
	mode := flag.String("m", "encode", "Mode")
	file := flag.String("f", "", "File path")
	rule := flag.Int("rule", 912, "Rule")
	pre := flag.Int("pre", 100, "Pre-rows")
	post := flag.Int("post", 100, "Post-rows")
	width := flag.Int("width", 1024, "Width")
	randPal := flag.Bool("rand", false, "Randomize colors")
	c0 := flag.String("c0", "25,25,55", "Color 0")
	c1 := flag.String("c1", "50,150,200", "Color 1")
	c2 := flag.String("c2", "220,100,40", "Color 2")
	flag.Parse()

	palette := [3]RGB{parseColor(*c0), parseColor(*c1), parseColor(*c2)}

	if *randPal && *mode == "encode" {
		rand.Seed(time.Now().UnixNano())
		palette = [3]RGB{
			{uint8(rand.Intn(256)), uint8(rand.Intn(256)), uint8(rand.Intn(256))},
			{uint8(rand.Intn(256)), uint8(rand.Intn(256)), uint8(rand.Intn(256))},
			{uint8(rand.Intn(256)), uint8(rand.Intn(256)), uint8(rand.Intn(256))},
		}
	}

	if *file == "" {
		fmt.Println("Error: File flag (-f) is required.")
		return
	}

	if *mode == "encode" {
		encode(*file, *pre, *post, *rule, *width, palette)
	} else {
		decode(*file, *pre, *rule, palette)
	}
}
