local Buffer = require("BitBuffer")
local HuffmanTree = require("HuffmanTree")

--markers:
local SOI = 0xD8 -- start of image
local EOI = 0xD9 -- end of image

local SOF0 = 0xC0 -- start of frame (baseline DCT, Discrete Cosine Transform)
local SOF1 = 0xC1 -- start of frame (extended sequential DCT)
local SOF2 = 0xC2 -- start of frame (progressive DCT)
local SOF3 = 0xC3 -- start of frame (lossless sequential DCT), SOF markers after SOF2 are usually unsupported

local DHT = 0xC4 -- define huffman tables
local DQT = 0xDB -- define quantization tables
local DAC = 0xCC -- define arithmetic coding conditions
local DRI = 0xDD -- define restart interval
local SOS = 0xDA -- start of scan
local DNL = 0xDC

local RSTnMin = 0xD0 -- restart
local RSTnMax = 0xD8
local APPn = 0xE0 -- application data (can be ignored)
local Comment = 0xFE

local JFIFHeader = 0xE0

-- zigzag diagonal matrix order in 1d array
local ZigZag = {
    1, 2, 6, 7, 15, 16, 28, 29,
    3, 5, 8, 14, 17, 27, 30, 43,
    4, 9, 13, 18, 26, 31, 42, 44,
    10, 12, 19, 25, 32, 41, 45, 54,
    11, 20, 24, 33, 40, 46, 53, 55,
    21, 23, 34, 39, 47, 52, 56, 61,
    22, 35, 38, 48, 51, 57, 60, 62,
    36, 37, 49, 50, 58, 59, 63, 64
}

--Tables and Info to decode image data
local QuantizationTables = {{}, {}, {}, {}}
local ACHuffmanCodes = {{}, {}, {}, {}}
local DCHuffmanCodes = {{}, {}, {}, {}}
local ComponantsInfo = {}
local HMax = 0 -- max horizontal sampling factor
local VMax = 0 -- max vertical sampling factor
local X = 0
local Y = 0
local SamplePrecision = 0
local RestartInterval = 0
local Blocks = {}
local Pixels = {}
local CosMap = {}

for i = 0, 7, 1 do
    CosMap[i] = {}
    for j = 0, 7, 1 do
        CosMap[i][j] = math.cos((2 * i + 1) * j * math.pi / 16)
    end
end

local Time = 0

function IDCT(Data) --optimize this later
    local Start = os.clock()
    local Result = {}
    local InvSqrt2 = 1 / math.sqrt(2)
    local Offset = SamplePrecision > 0 and 1 << (SamplePrecision - 1) or 1

    for y = 0, 7, 1 do
        for x = 0, 7, 1 do

            local S = 0

            for u = 0, 7, 1 do
                for v = 0, 7, 1 do
                    S = S + (u == 0 and InvSqrt2 or 1) * (v == 0 and InvSqrt2 or 1) * Data[u * 8 + v + 1] * CosMap[x][u] * CosMap[y][v]
                end
            end

            Result[x * 8 + y + 1] = S / 4 + Offset

        end
    end

    Time = Time + (os.clock() - Start)

    return Result
end

function YCbCrToRGB()

    local Offset = SamplePrecision > 0 and 1 << (SamplePrecision - 1) or 1
    local Max = Offset * 2 - 1

    local function Clamp(x)
        if (x > Max) then return Max end
        if (x < 0) then return 0 end
        return x
    end

    for i = 1, Y, 1 do
        for j = 1, X, 1 do
            local Index = (i-1) * X + j
            local y = Pixels[1][Index] or Offset
            local Cb = Pixels[2][Index] or Offset
            local Cr = Pixels[3][Index] or Offset

            local R = Clamp(y + 1.402 * (Cr - Offset))
            local G = Clamp(y - 0.34414 * (Cb - Offset) - 0.71414 * (Cr - Offset))
            local B = Clamp(y + 1.772 * (Cb - Offset))

            Pixels[1][Index] = math.floor(R + 0.5)
            Pixels[2][Index] = math.floor(G + 0.5)
            Pixels[3][Index] = math.floor(B + 0.5)
        end
    end
end

function ReadQuantizationTables(Buff)
    local Length = Buff:ReadBytes(2) - 2 --length bytes are counted in the length of chunk

    while (Length > 0) do --there may be multiple quantization tables in one block
        local Precision = Buff:ReadBits(4) == 0 and 1 or 2
        local Tq = Buff:ReadBits(4)
        local QuantizationTable = {}
        Length = Length - 1

        for v = 1, 64, 1 do
            QuantizationTable[v] = Buff:ReadBytes(Precision)
        end

        Length = Length - Precision * 64
        QuantizationTables[Tq + 1] = QuantizationTable
    end

end

function ReadHuffmanTable(Buff)
    local Length = Buff:ReadBytes(2) - 2

    while (Length > 0) do
        local TableClass = Buff:ReadBits(4)
        local Dest = Buff:ReadBits(4)
        local CodeLengths = {}
        local GeneratedHuffmanCodes = HuffmanTree.New()
        local CurrentCode = 0

        for i = 1, 16, 1 do
            CodeLengths[i] = Buff:ReadBytes(1)
        end

        Length = Length - 17

        for i = 1, 16, 1 do --generating huffman codes from length frequencies
            for j = 1, CodeLengths[i], 1 do
                local Value = Buff:ReadBytes(1)
                GeneratedHuffmanCodes:AddCode(CurrentCode, i, Value)
                CurrentCode = CurrentCode + 1
            end
            Length = Length - CodeLengths[i]
            CurrentCode = CurrentCode << 1
        end

        (TableClass == 1 and ACHuffmanCodes or DCHuffmanCodes)[Dest + 1] = GeneratedHuffmanCodes --didnt know I could use the ternary operator like this lol
    end

end

function ReadJFIFHeader(Buff)
    local Length = Buff:ReadBytes(2)
    local Identfier = Buff:ReadBytes(5)

    if (Identfier ~= 0x4A46494600) then --skip the thumbnail chunk if present
        Buff:ReadBytes(Length - 7)
        return
    end

    local Version = Buff:ReadBytes(2)
    local Density = Buff:ReadBytes(1)

    local XDensity = Buff:ReadBytes(2)
    local YDensity = Buff:ReadBytes(2)

    local XThumbnail = Buff:ReadBytes(1)
    local YThumbnail = Buff:ReadBytes(1)

    Buff:ReadBytes(XThumbnail * YThumbnail) -- skip thumbnail data

    print(XDensity, YDensity, Density, Version)
end

function ReadFrame(Buff)
    local Length = Buff:ReadBytes(2)
    local Precision = Buff:ReadBytes(1)

    SamplePrecision = Precision

    Y = Buff:ReadBytes(2)
    X = Buff:ReadBytes(2)

    local ComponantsInFrame = Buff:ReadBytes(1)

    for i = 1, ComponantsInFrame, 1 do
        local Identifier = Buff:ReadBytes(1)

        local Componant = {
            HorizontalSamplingFactor = Buff:ReadBits(4),
            VerticalSamplingFactor = Buff:ReadBits(4),
            QuantizationTableDestination = Buff:ReadBytes(1)
        }

        if (Componant.HorizontalSamplingFactor > HMax) then
            HMax = Componant.HorizontalSamplingFactor
        end

        if (Componant.VerticalSamplingFactor > VMax) then
            VMax = Componant.VerticalSamplingFactor
        end

        ComponantsInfo[Identifier] = Componant
        Pixels[i] = {}
    end

    --initializing blocks
    for p, c in pairs(ComponantsInfo) do
        -- may have extra blocks from expanding caused by sampling factors (encoder may enforce
        -- componant dimensions to be a multiple of the sampling factors and pad blocks) 
        -- (ONLY SOMETIMES), may be ommitted as well depending on the encoder (seriously, wtf)
        -- "solved" by making a temp block if indexed block is nil while reading scan
        local BlocksXDim = math.max(c.HorizontalSamplingFactor, math.ceil(math.ceil(X * c.HorizontalSamplingFactor / HMax) / 8))
        local BlocksYDim = math.max(c.VerticalSamplingFactor, math.ceil(math.ceil(Y * c.VerticalSamplingFactor / VMax) / 8))
        Blocks[p] = {}
        Blocks[p].X = BlocksXDim
        Blocks[p].Y = BlocksYDim

        local NumComponantBlocks = BlocksXDim * BlocksYDim
        for i = 1, NumComponantBlocks, 1 do
            local Block = {}
            for v = 1, 64, 1 do
                Block[v] = 0
            end
            Blocks[p][i] = Block
        end
    end

    print("Size:", X, Y, ComponantsInFrame, HMax, VMax)
end

function IndexHuffmanTree(Tree, Buff)
    local Current = Tree.Root

    while (Current.Value == nil) do
        Current = Current[Buff:ReadBit()]
    end

    return Current.Value
end

function Extend(V, T) -- Extend function as defined in the Jpeg spec (ITU T.81)
    if (T == 0) then return 0 end
    return V < (1 << (T - 1)) and V - (1 << T) + 1 or V
end

function ReadSpectralScan(Buff, Ss, Se, Al, Ah, ComponantsInScan, ComponantParameters) --handles basline and initial scans of progressive jpegs
    local PreviousDCCoefficients = {}

    local ScanHMax = 1
    local ScanVMax = 1

    for i = 1, ComponantsInScan, 1 do
        local ComponantParams = ComponantParameters[1]
        local ComponantInfo = ComponantsInfo[ComponantParams.ScanComponantIndex]
        if (ComponantInfo.HorizontalSamplingFactor > ScanHMax) then
            ScanHMax = ComponantInfo.HorizontalSamplingFactor
        end

        if (ComponantInfo.VerticalSamplingFactor > ScanVMax) then
            ScanVMax = ComponantInfo.VerticalSamplingFactor
        end
    end

    local MCUXDim = math.ceil(X / (8 * ScanHMax))
    local MCUYDim = math.ceil(Y / (8 * ScanVMax))

    if (ComponantsInScan > 1) then
        TotalMCUs = MCUXDim * MCUYDim
    else
        local Comp = Blocks[ComponantParameters[1].ScanComponantIndex]
        TotalMCUs = Comp.X * Comp.Y
    end

    for i = 1, ComponantsInScan, 1 do
        PreviousDCCoefficients[i] = 0
    end

    local EndOfBandRun = 0

    for MCU = 1, TotalMCUs, 1 do
        for i = 1, ComponantsInScan, 1 do
            local ComponantParams = ComponantParameters[i]
            local ComponantInfo = ComponantsInfo[ComponantParams.ScanComponantIndex]
            local ACHuffmanTree = ACHuffmanCodes[ComponantParams.ACTableIndex + 1]
            local DCHuffmanTree = DCHuffmanCodes[ComponantParams.DCTableIndex + 1]

            local NumComponantBlocks = ComponantsInScan > 1 and ComponantInfo.HorizontalSamplingFactor * ComponantInfo.VerticalSamplingFactor or 1

            if ((ACHuffmanTree.Root == nil and Se > 0) or (DCHuffmanTree.Root == nil and Ss == 0)) then
                print("undefined AC/DC huffman tree")
                os.exit(1)
            end

            for c = 1, NumComponantBlocks, 1 do
                local BlockData
                local K = Ss + 1

                -- finding block index and dealing with edge case
                local BlocksXDim = Blocks[ComponantParams.ScanComponantIndex].X
                local BlocksYDim = Blocks[ComponantParams.ScanComponantIndex].Y

                if (ComponantsInScan > 1) then
                    local MCUYIndex = (MCU-1) // MCUXDim
                    local MCUXIndex = (MCU-1) - MCUYIndex * MCUXDim
                    local BlockY = MCUYIndex * ComponantInfo.VerticalSamplingFactor + (c-1) // ComponantInfo.HorizontalSamplingFactor
                    local BlockX = MCUXIndex * ComponantInfo.HorizontalSamplingFactor + ((c-1) % ComponantInfo.HorizontalSamplingFactor) + 1

                    if (BlockX <= BlocksXDim and BlockY <= BlocksYDim) then
                        BlockData = Blocks[ComponantParams.ScanComponantIndex][BlockY * BlocksXDim + BlockX]
                    end
                else
                    local MCUYIndex = (MCU-1) // BlocksXDim
                    local MCUXIndex = (MCU-1) - MCUYIndex * BlocksXDim

                    if (MCUXIndex <= BlocksXDim and MCUYIndex <= BlocksYDim) then
                        BlockData = Blocks[ComponantParams.ScanComponantIndex][MCU]
                    end
                end

                --problem when padding blocks are added by some encoders, worked around by creating temp blocks to throw away padding
                if (BlockData == nil) then
                    BlockData = {}
                    for v = 1, 64, 1 do
                        BlockData[v] = 0
                    end
                end

                if (EndOfBandRun == 0) then

                    if (Ss == 0) then
                        local T = IndexHuffmanTree(DCHuffmanTree, Buff)
                        local DIFF = Extend(Buff:ReadBits(T), T) + PreviousDCCoefficients[i]
                        PreviousDCCoefficients[i] = DIFF

                        BlockData[K] = BlockData[K] + DIFF * (1 << Al)
                        K = K + 1
                    end

                    while (K <= Se + 1) do
                        local RS = IndexHuffmanTree(ACHuffmanTree, Buff)
                        local LowerNibble = RS & 0xF
                        local HigherNibble = RS >> 4

                        if (LowerNibble == 0) then

                            if (HigherNibble == 15) then
                                K = K + 16
                            else
                                EndOfBandRun = (1 << HigherNibble) + Buff:ReadBits(HigherNibble) - 1
                                break
                            end

                        else

                            K = K + HigherNibble

                            BlockData[K] = BlockData[K] + Extend(Buff:ReadBits(LowerNibble), LowerNibble) * (1 << Al)
                            K = K + 1

                        end
                    end
                else
                    EndOfBandRun = EndOfBandRun - 1
                end

            end
        end

        if (RestartInterval ~= 0 and MCU % RestartInterval == 0) then
            Buff:Align()
            local Marker = Buff:ReadBytes(2)

            if (Marker ~= RSTnMin + ((RestartInterval // RestartInterval) % 8)) then
                print("Restart Marker error, got marker", Marker, "expected", 0xFFD0 + ((RestartInterval // RestartInterval) % 8))
                return
            end

            EndOfBandRun = 0

            for i = 1, ComponantsInScan, 1 do
                PreviousDCCoefficients[i] = 0
            end
        end

    end

end

function ReadRefinementScan(Buff, Ss, Se, Al, Ah, ComponantsInScan, ComponantParameters)
    local TotalMCUs
    local EndOfBandRun = 0
    local Positive = 1 << Al
    local Negative = -1 * Positive

    local ScanHMax = 1
    local ScanVMax = 1

    for i = 1, ComponantsInScan, 1 do
        local ComponantParams = ComponantParameters[1]
        local ComponantInfo = ComponantsInfo[ComponantParams.ScanComponantIndex]
        if (ComponantInfo.HorizontalSamplingFactor > ScanHMax) then
            ScanHMax = ComponantInfo.HorizontalSamplingFactor
        end

        if (ComponantInfo.VerticalSamplingFactor > ScanVMax) then
            ScanVMax = ComponantInfo.VerticalSamplingFactor
        end
    end

    local MCUXDim = math.ceil(X / (8 * ScanHMax))
    local MCUYDim = math.ceil(Y / (8 * ScanVMax))

    if (ComponantsInScan > 1) then
        TotalMCUs = MCUXDim * MCUYDim
    else
        local Comp = Blocks[ComponantParameters[1].ScanComponantIndex]
        TotalMCUs = Comp.X * Comp.Y
    end

    for MCU = 1, TotalMCUs, 1 do
        for i = 1, ComponantsInScan, 1 do
            local ComponantParams = ComponantParameters[i]
            local ComponantInfo = ComponantsInfo[ComponantParams.ScanComponantIndex]
            local ACHuffmanTree = ACHuffmanCodes[ComponantParams.ACTableIndex + 1]

            local NumComponantBlocks = ComponantsInScan > 1 and ComponantInfo.HorizontalSamplingFactor * ComponantInfo.VerticalSamplingFactor or 1

            if (ACHuffmanTree.Root == nil and Se > 0) then
                print("undefined AC huffman tree")
                os.exit(1)
            end

            for c = 1, NumComponantBlocks, 1 do
                local BlockData
                local K = Ss + 1

                -- finding block index and dealing with edge case
                local BlocksXDim = Blocks[ComponantParams.ScanComponantIndex].X
                local BlocksYDim = Blocks[ComponantParams.ScanComponantIndex].Y

                if (ComponantsInScan > 1) then
                    local MCUYIndex = (MCU-1) // MCUXDim
                    local MCUXIndex = (MCU-1) - MCUYIndex * MCUXDim
                    local BlockY = MCUYIndex * ComponantInfo.VerticalSamplingFactor + (c-1) // ComponantInfo.HorizontalSamplingFactor
                    local BlockX = MCUXIndex * ComponantInfo.HorizontalSamplingFactor + ((c-1) % ComponantInfo.HorizontalSamplingFactor) + 1

                    if (BlockX <= BlocksXDim and BlockY <= BlocksYDim) then
                        BlockData = Blocks[ComponantParams.ScanComponantIndex][BlockY * BlocksXDim + BlockX]
                    end
                else
                    local MCUYIndex = (MCU-1) // BlocksXDim
                    local MCUXIndex = (MCU-1) - MCUYIndex * BlocksXDim

                    if (MCUXIndex <= BlocksXDim and MCUYIndex <= BlocksYDim) then
                        BlockData = Blocks[ComponantParams.ScanComponantIndex][MCU]
                    end
                end

                --problem when padding blocks are added by some encoders
                if (BlockData == nil) then
                    BlockData = {}
                    for v = 1, 64, 1 do
                        BlockData[v] = 0
                    end
                end

                if (EndOfBandRun <= 0) then

                    if (Ss == 0) then
                        local Bit = Buff:ReadBit()

                        if (BlockData[K] == 0) then
                            BlockData[K] = (Bit == 0 and Negative or Positive)
                        else
                            BlockData[K] = BlockData[K] + (BlockData[K] < 0 and Negative or Positive)
                        end

                        K = K + 1
                        if (Se ~= 0) then print("invalid refinement scan, DC and AC coeffecients are mixed") os.exit(1) end
                    end

                    while (K <= Se + 1) do
                        local RS = IndexHuffmanTree(ACHuffmanTree, Buff)
                        local LowerNibble = RS & 0xF
                        local HigherNibble = RS >> 4

                        if (LowerNibble == 0) then
                            if (HigherNibble == 15) then
                                local Skip = 16

                                while (Skip > 0 and K <= Se+1) do
                                    if (BlockData[K] ~= 0) then
                                        BlockData[K] = BlockData[K] + Buff:ReadBit() * (BlockData[K] < 0 and Negative or Positive)
                                    else
                                        Skip = Skip - 1
                                    end
                                    K = K + 1
                                end

                            else
                                EndOfBandRun = (1 << HigherNibble) + Buff:ReadBits(HigherNibble) - 1

                                while (K <= Se + 1) do
                                    if (BlockData[K] ~= 0) then
                                        BlockData[K] = BlockData[K] + Buff:ReadBit() * (BlockData[K] < 0 and Negative or Positive)
                                    end
                                    K = K + 1
                                end

                                break
                            end

                        else

                            local Skip = HigherNibble
                            local Sign = Buff:ReadBits(LowerNibble) == 1 and 1 or -1

                            while ((Skip > 0 or BlockData[K] ~= 0) and K <= Se+1) do
                                -- need to pass a minimumm of skip coeffecients, but must continue to skip until a 0 value is found to place the new AC coefficent
                                -- this took A WEEK to figure out
                                if (BlockData[K] ~= 0) then
                                    BlockData[K] = BlockData[K] + Buff:ReadBit() * (BlockData[K] < 0 and Negative or Positive)
                                else
                                    Skip = Skip - 1
                                end
                                K = K + 1
                            end

                            if (K > Se + 1) then break end

                            BlockData[K] = BlockData[K] + Sign * (1 << Al)
                            K = K + 1

                        end
                    end
                else
                     while (K <= Se + 1) do
                        if (BlockData[K] ~= 0) then
                            BlockData[K] = BlockData[K] + (Buff:ReadBit() << Al) * (BlockData[K] < 0 and -1 or 1)
                        end
                        K = K + 1
                    end
                    EndOfBandRun = EndOfBandRun - 1
                end

            end
        end

        if (RestartInterval ~= 0 and MCU % RestartInterval == 0) then
            Buff:Align()
            local Marker = Buff:ReadBytes(2)

            if (Marker ~= RSTnMin + ((RestartInterval // RestartInterval) % 8)) then
                print("Restart Marker error, got marker", Marker, "expected", 0xFFD0 + ((RestartInterval // RestartInterval) % 8))
                return
            end

            EndOfBandRun = 0
        end

    end
end

function ReadScan(Buff)
    local Length = Buff:ReadBytes(2)
    local ComponantsInScan = Buff:ReadBytes(1)
    local ComponantParameters = {}

    for i = 1, ComponantsInScan, 1 do
        local Parameters = {
            ScanComponantIndex = Buff:ReadBytes(1),
            DCTableIndex = Buff:ReadBits(4),
            ACTableIndex = Buff:ReadBits(4)
        }

        ComponantParameters[i] = Parameters
    end

    local Ss = Buff:ReadBytes(1) -- start of spectral selection
    local Se = Buff:ReadBytes(1) -- end of spectral selection

    local Ah = Buff:ReadBits(4) -- successive approximation high
    local Al = Buff:ReadBits(4) -- successive approximation low

    if (Ah == 0) then --clean up scan code later...
        ReadSpectralScan(Buff, Ss, Se, Al, Ah, ComponantsInScan, ComponantParameters)
    else
        print("reading refinement")
        ReadRefinementScan(Buff, Ss, Se, Al, Ah, ComponantsInScan, ComponantParameters)
    end

end

function ReadRestartInterval(Buff)
    local Length = Buff:ReadBytes(2)
    RestartInterval = Buff:ReadBytes(2) --number of MCU in the restart interval
end

function ReadDNL(Buff)
    local Length = Buff:ReadBytes(2)
    local NumLines = Buff:ReadBytes(2)
end

function InterpretMarker(Buff) --handles calling functions to decode markers
    local Marker = Buff:ReadBytes(1)

    if (Marker == DQT) then
        print("Define Quantization Tables")
        ReadQuantizationTables(Buff)
    elseif (Marker == DHT) then
        ReadHuffmanTable(Buff)
        print("Define Huffman Tables")
    elseif (Marker == JFIFHeader) then
        print("JFIF header")
        ReadJFIFHeader(Buff)
    elseif (Marker == SOF0 or Marker == SOF1 or Marker == SOF2) then
        print("Start of frame (baseline DCT or progressive DCT)")
        ReadFrame(Buff)
    elseif (Marker == SOS) then
        print("Start of scan")
        ReadScan(Buff)
        Buff:Align()
    elseif (Marker == DRI) then
        print("restart len")
        ReadRestartInterval(Buff)
    elseif (Marker == EOI) then
        return -1
    elseif (Marker == DAC) then
        print("Arithmetic encoding is not supported")
        os.exit(1)
    elseif (Marker == DNL) then
        print("DNL")
        ReadDNL(Buff)
    elseif (Marker ~= 0) then --0xFF00 is a padding byte
        local Len = Buff:ReadBytes(2) - 2 --skip marker

        if (SOF2 < Marker and Marker <= 0xCF) then
            print("Unsupported frame:", Marker)
            os.exit(1)
        end

        Buff:ReadBytes(Len)
    end

end

function TransformBlocks()

    for c, info in pairs(ComponantsInfo) do
        local NumComponantBlocks = #Blocks[c]
        local QuantizationTable = QuantizationTables[info.QuantizationTableDestination+1]

        --un-zigzag, dequantize and IDCT
        for i = 1, NumComponantBlocks, 1 do
            local DecodedBlock = Blocks[c][i]
            local Block = {}
            for v = 1, 64, 1 do
                Block[v] = DecodedBlock[ZigZag[v]] * QuantizationTable[ZigZag[v]]
            end
            Blocks[c][i] = IDCT(Block)
        end

        --upsample and map to pixel matrix
        local XScale = HMax // info.HorizontalSamplingFactor
        local YScale = VMax // info.VerticalSamplingFactor
        local SubImageX = XScale * 8
        local SubImageY = YScale * 8

        for yb = 1, Blocks[c].Y, 1 do
            for xb = 1, Blocks[c].X, 1 do
                local BlockIndex = (yb-1) * Blocks[c].X + xb
                local Block = Blocks[c][BlockIndex]

                local HorizontalEdge = math.min(SubImageY, (Y - ((yb - 1) * SubImageY)))

                for y = 1, HorizontalEdge, 1 do
                    local VerticalEdge = math.min(SubImageX, (X - ((xb - 1) * SubImageX)))
                    for x = 1, VerticalEdge, 1 do
                        local ImageYIndex = (yb - 1) * SubImageY + (y - 1)
                        local ImageXIndex = (xb - 1) * SubImageX + (x - 1)
                        local BlockYIndex = (y - 1) // YScale
                        local BlockXIndex = (x - 1) // XScale

                        Pixels[c][ImageYIndex * X + ImageXIndex + 1] = Block[BlockYIndex * 8 + BlockXIndex + 1]
                    end
                end

            end
        end

    end

end

function DecodeJpeg(FileName)
    local Buff = Buffer.New(FileName)

    if (Buff:ReadBytes(2) ~= 0xFFD8) then print("inavlid jpg file") return end

    local ImageInfo = {
        X = X,
        Y = Y,
        Pixels = Pixels,
        QuantizationTables = {{}, {}, {}, {}},
        DCHuffmanCodes = {{}, {}, {}, {}},
        ACHuffmanCodes = {{}, {}, {}, {}},
        ComponantsInfo = {},
        HMax = 0,
        VMax = 0,
        SamplePrecision = 0,
        RestartInterval = 0,
        Blocks = {},
    }

    while (not Buff:IsEmpty()) do
        local Byte = Buff:ReadBytes(1)
        if (Byte == 0xFF) then
            local R = InterpretMarker(Buff)

            if (R == -1) then
                break
            end

        end
    end

    TransformBlocks()
    YCbCrToRGB()

    ImageInfo.X = X
    ImageInfo.Y = Y

    --reset tables/data used for decoding
    QuantizationTables = {{}, {}, {}, {}}
    DCHuffmanCodes = {{}, {}, {}, {}}
    ACHuffmanCodes = {{}, {}, {}, {}}
    ComponantsInfo = {}
    X = 0
    Y = 0
    HMax = 0
    VMax = 0
    SamplePrecision = 0
    RestartInterval = 0
    MCUs = {}
    Pixels = {}

    return ImageInfo
end

local S = os.clock()
local ImageInfo = DecodeJpeg("jpegtest.jpg")

print("Decoding time:", os.clock() - S)

function WritePPM(File, Length, Width)
    File:write("P3\n")
    File:write(tostring(Width).." "..tostring(Length).."\n")
    File:write("255\n")
    for l = 1, Length, 1 do
        for w = 1, Width, 1 do
            local Index = (l - 1) * Width + w
            local R = ImageInfo.Pixels[1][Index]
            local G = ImageInfo.Pixels[2][Index]
            local B = ImageInfo.Pixels[3][Index]

            File:write(tostring(R).." "..tostring(G).." "..tostring(B).."\n")
        end
    end
end

WritePPM(io.open("t.ppm", "w"), ImageInfo.Y, ImageInfo.X)

print("IDCT time:", Time)

return DecodeJpeg
