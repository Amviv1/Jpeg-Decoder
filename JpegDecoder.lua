local Buffer = require("BitBuffer")
local HuffmanTree = require("HuffmanTree")
local IDCT = require("IDCT")

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

function YCbCrToRGB(ImageInfo)
    local Pixels = ImageInfo.Pixels
    local Offset = ImageInfo.SamplePrecision > 0 and 1 << (ImageInfo.SamplePrecision - 1) or 0
    local Max = Offset * 2 - 1

    local function Clamp(x)
        if (x > Max) then return Max end
        if (x < 0) then return 0 end
        return x
    end

    local Index = 1

    for i = 1, ImageInfo.Y, 1 do
        for j = 1, ImageInfo.X, 1 do
            local y = Pixels[1][Index]
            local Cb = Pixels[2][Index] - Offset
            local Cr = Pixels[3][Index] - Offset

            local R = Clamp(y + 1.402 * Cr)
            local G = Clamp(y - 0.34414 * Cb - 0.71414 * Cr)
            local B = Clamp(y + 1.772 * Cb)

            Pixels[1][Index] = math.floor(R + 0.5)
            Pixels[2][Index] = math.floor(G + 0.5)
            Pixels[3][Index] = math.floor(B + 0.5)

            Index = Index + 1
        end
    end
end

function ReadQuantizationTables(Buff, ImageInfo)
    local Length = Buff:ReadBytes(2) - 2 --length bytes are counted in the length of chunk

    while (Length > 0) do --there may be multiple quantization tables in one chunk
        local Precision = Buff:ReadBits(4) == 0 and 1 or 2
        local Tq = Buff:ReadBits(4)
        local QuantizationTable = {}
        Length = Length - 1

        for v = 1, 64, 1 do
            QuantizationTable[v] = Buff:ReadBytes(Precision)
        end

        Length = Length - Precision * 64
        ImageInfo.QuantizationTables[Tq + 1] = QuantizationTable
    end

end

function ReadHuffmanTable(Buff, ImageInfo)
    local Length = Buff:ReadBytes(2) - 2

    while (Length > 0) do -- may have multiple huffman tables in one chunk
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

        if (TableClass == 1) then
            ImageInfo.ACHuffmanCodes[Dest + 1] = GeneratedHuffmanCodes
        else
            ImageInfo.DCHuffmanCodes[Dest + 1] = GeneratedHuffmanCodes
        end

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

end

function ReadFrame(Buff, ImageInfo)
    local Length = Buff:ReadBytes(2)
    local Precision = Buff:ReadBytes(1)

    ImageInfo.SamplePrecision = Precision

    ImageInfo.Y = Buff:ReadBytes(2)
    ImageInfo.X = Buff:ReadBytes(2)
    ImageInfo.HMax = 1
    ImageInfo.VMax = 1

    local ComponantsInFrame = Buff:ReadBytes(1)

    for i = 1, ComponantsInFrame, 1 do
        local Identifier = Buff:ReadBytes(1)

        local Componant = {
            HorizontalSamplingFactor = Buff:ReadBits(4),
            VerticalSamplingFactor = Buff:ReadBits(4),
            QuantizationTableDestination = Buff:ReadBytes(1)
        }

        if (Componant.HorizontalSamplingFactor > ImageInfo.HMax) then
            ImageInfo.HMax = Componant.HorizontalSamplingFactor
        end

        if (Componant.VerticalSamplingFactor > ImageInfo.VMax) then
            ImageInfo.VMax = Componant.VerticalSamplingFactor
        end

        ImageInfo.ComponantsInfo[Identifier] = Componant
        ImageInfo.Pixels[i] = {}
    end

    --initializing blocks
    for p, c in pairs(ImageInfo.ComponantsInfo) do
        -- may have extra blocks from expanding caused by sampling factors (encoder may enforce componant dimensions to be a 
        -- multiple of the sampling factors and pad blocks). (ONLY SOMETIMES), may be ommitted as well depending on the encoder,
        -- solved by making 'temporary' blocks within scans when the MCU is outisde of image bounds
        local BlocksXDim = math.ceil(math.ceil(ImageInfo.X / 8) * (c.HorizontalSamplingFactor / ImageInfo.HMax))
        local BlocksYDim = math.ceil(math.ceil(ImageInfo.Y / 8) * (c.VerticalSamplingFactor / ImageInfo.VMax))
        ImageInfo.Blocks[p] = {}
        ImageInfo.Blocks[p].X = BlocksXDim
        ImageInfo.Blocks[p].Y = BlocksYDim

        local NumComponantBlocks = BlocksXDim * BlocksYDim
        for i = 1, NumComponantBlocks, 1 do
            local Block = {}
            for v = 1, 64, 1 do
                Block[v] = 0
            end
            ImageInfo.Blocks[p][i] = Block
        end
    end

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

function ScanDimensions(ComponantsInScan, ComponantParameters, ImageInfo)
    local ScanHMax = 1
    local ScanVMax = 1

    for i = 1, ComponantsInScan, 1 do
        local ComponantParams = ComponantParameters[1]
        local ComponantInfo = ImageInfo.ComponantsInfo[ComponantParams.ScanComponantIndex]
        if (ComponantInfo.HorizontalSamplingFactor > ScanHMax) then
            ScanHMax = ComponantInfo.HorizontalSamplingFactor
        end

        if (ComponantInfo.VerticalSamplingFactor > ScanVMax) then
            ScanVMax = ComponantInfo.VerticalSamplingFactor
        end
    end

    local MCUXDim = math.ceil(ImageInfo.X / (8 * ScanHMax))
    local MCUYDim = math.ceil(ImageInfo.Y / (8 * ScanVMax))
    local TotalMCUs

    if (ComponantsInScan > 1) then
        TotalMCUs = MCUXDim * MCUYDim
    else
        local CInfo = ImageInfo.ComponantsInfo[ComponantParameters[1].ScanComponantIndex]
        -- not sure if the dimension calculations for blocks work 100% of the time
        TotalMCUs = math.max(CInfo.HorizontalSamplingFactor, math.ceil(math.ceil(ImageInfo.X * CInfo.HorizontalSamplingFactor / ImageInfo.HMax) / 8)) *
                    math.max(CInfo.VerticalSamplingFactor, math.ceil(math.ceil(ImageInfo.Y * CInfo.VerticalSamplingFactor / ImageInfo.VMax) / 8))
    end

    return MCUXDim, TotalMCUs
end

function ReadSpectralScan(Buff, Ss, Se, Al, Ah, ComponantsInScan, ComponantParameters, ImageInfo) --handles basline and spectral scans in progressive jpegs
    local MCUXDim, TotalMCUs = ScanDimensions(ComponantsInScan, ComponantParameters, ImageInfo)
    local RestartInterval = ImageInfo.RestartInterval
    local PreviousDCCoefficients = {}
    local EndOfBandRun = 0

    for i = 1, ComponantsInScan, 1 do
        PreviousDCCoefficients[i] = 0
    end

    for MCU = 1, TotalMCUs, 1 do
        for i = 1, ComponantsInScan, 1 do
            local ComponantParams = ComponantParameters[i]
            local ComponantInfo = ImageInfo.ComponantsInfo[ComponantParams.ScanComponantIndex]
            local ACHuffmanTree = ImageInfo.ACHuffmanCodes[ComponantParams.ACTableIndex + 1]
            local DCHuffmanTree = ImageInfo.DCHuffmanCodes[ComponantParams.DCTableIndex + 1]

            local NumComponantBlocks = ComponantsInScan > 1 and ComponantInfo.HorizontalSamplingFactor * ComponantInfo.VerticalSamplingFactor or 1

            for c = 1, NumComponantBlocks, 1 do
                if (EndOfBandRun > 0 and EndOfBandRun - (NumComponantBlocks - c + 1) >= 0) then
                    EndOfBandRun = EndOfBandRun - (NumComponantBlocks - c + 1)
                    break
                else
                    c = c + EndOfBandRun
                    EndOfBandRun = 0
                end

                local BlockData
                local K = Ss + 1

                -- finding block index and dealing with edge case
                local BlocksXDim = ImageInfo.Blocks[ComponantParams.ScanComponantIndex].X
                local BlocksYDim = ImageInfo.Blocks[ComponantParams.ScanComponantIndex].Y

                if (ComponantsInScan > 1) then
                    local MCUYIndex = (MCU-1) // MCUXDim
                    local MCUXIndex = (MCU-1) - MCUYIndex * MCUXDim
                    local BlockY = MCUYIndex * ComponantInfo.VerticalSamplingFactor + (c-1) // ComponantInfo.HorizontalSamplingFactor
                    local BlockX = MCUXIndex * ComponantInfo.HorizontalSamplingFactor + ((c-1) % ComponantInfo.HorizontalSamplingFactor) + 1

                    if (BlockX <= BlocksXDim and BlockY <= BlocksYDim) then
                        BlockData = ImageInfo.Blocks[ComponantParams.ScanComponantIndex][BlockY * BlocksXDim + BlockX]
                    end
                else
                    local MCUYIndex = (MCU-1) // BlocksXDim
                    local MCUXIndex = (MCU-1) - MCUYIndex * BlocksXDim

                    if (MCUXIndex <= BlocksXDim and MCUYIndex <= BlocksYDim) then
                        BlockData = ImageInfo.Blocks[ComponantParams.ScanComponantIndex][MCU]
                    end
                end

                if (BlockData == nil) then
                    BlockData = {}
                    for l = 1, 64, 1 do
                        BlockData[l] = 0
                    end
                end

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

            end
        end

        -- note: restart marker is skipped if we finished decoding all MCUs
        if (RestartInterval ~= 0 and MCU % RestartInterval == 0 and MCU ~= TotalMCUs) then
            Buff:Align()

            local ExpextedMarker = 0xFF00 + RSTnMin + (((MCU - RestartInterval) // RestartInterval) % 8)
            local Marker = Buff:ReadBytes(2)

            if (Marker ~= ExpextedMarker) then
                print("Restart Marker error, got marker", Marker, "expected", ExpextedMarker)
                return
            end

            EndOfBandRun = 0

            for i = 1, ComponantsInScan, 1 do
                PreviousDCCoefficients[i] = 0
            end
        end

    end

end

function ReadRefinementScan(Buff, Ss, Se, Al, Ah, ComponantsInScan, ComponantParameters, ImageInfo)
    local EndOfBandRun = 0
    local RestartInterval = ImageInfo.RestartInterval
    local Positive = 1 << Al
    local Negative = -1 * Positive

    local MCUXDim, TotalMCUs = ScanDimensions(ComponantsInScan, ComponantParameters, ImageInfo)

    for MCU = 1, TotalMCUs, 1 do
        for i = 1, ComponantsInScan, 1 do
            local ComponantParams = ComponantParameters[i]
            local ComponantInfo = ImageInfo.ComponantsInfo[ComponantParams.ScanComponantIndex]
            local ACHuffmanTree = ImageInfo.ACHuffmanCodes[ComponantParams.ACTableIndex + 1]

            local NumComponantBlocks = ComponantsInScan > 1 and ComponantInfo.HorizontalSamplingFactor * ComponantInfo.VerticalSamplingFactor or 1

            for c = 1, NumComponantBlocks, 1 do

                local BlockData
                local K = Ss + 1

                -- finding block index and dealing with edge case
                local BlocksXDim = ImageInfo.Blocks[ComponantParams.ScanComponantIndex].X
                local BlocksYDim = ImageInfo.Blocks[ComponantParams.ScanComponantIndex].Y

                if (ComponantsInScan > 1) then
                    local MCUYIndex = (MCU-1) // MCUXDim
                    local MCUXIndex = (MCU-1) - MCUYIndex * MCUXDim
                    local BlockY = MCUYIndex * ComponantInfo.VerticalSamplingFactor + (c-1) // ComponantInfo.HorizontalSamplingFactor
                    local BlockX = MCUXIndex * ComponantInfo.HorizontalSamplingFactor + ((c-1) % ComponantInfo.HorizontalSamplingFactor) + 1

                    if (BlockX <= BlocksXDim and BlockY <= BlocksYDim) then
                        BlockData = ImageInfo.Blocks[ComponantParams.ScanComponantIndex][BlockY * BlocksXDim + BlockX]
                    end
                else
                    local MCUYIndex = (MCU-1) // BlocksXDim
                    local MCUXIndex = (MCU-1) - MCUYIndex * BlocksXDim

                    if (MCUXIndex <= BlocksXDim and MCUYIndex <= BlocksYDim) then
                        BlockData = ImageInfo.Blocks[ComponantParams.ScanComponantIndex][MCU]
                    end
                end

                if (BlockData == nil) then
                    BlockData = {}
                    for l = 1, 64, 1 do
                        BlockData[l] = 0
                    end
                 end

                if (Ss == 0 and EndOfBandRun == 0) then
                    local Bit = Buff:ReadBit()

                    if (BlockData[K] == 0) then
                        BlockData[K] = (Bit == 0 and Negative or Positive)
                    else
                        BlockData[K] = BlockData[K] + (BlockData[K] < 0 and Negative or Positive)
                    end

                    K = K + 1
                    if (Se ~= 0) then print("invalid refinement scan, DC and AC coeffecients are mixed") os.exit(1) end
                end

                while (K <= Se + 1 and EndOfBandRun == 0) do
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
                            EndOfBandRun = (1 << HigherNibble) + Buff:ReadBits(HigherNibble)
                            break
                        end
                    else
                        local Skip = HigherNibble
                        local Sign = Buff:ReadBits(LowerNibble) == 1 and 1 or -1

                        while ((Skip > 0 or BlockData[K] ~= 0) and K <= Se+1) do
                            -- need to pass a minimumm of skip coeffecients, but must continue to skip until a 0 value is found to place the new AC coefficent
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

                if (EndOfBandRun > 0) then
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

        -- note: restart marker is skipped if we finished decoding all MCUs
        if (ImageInfo.RestartInterval ~= 0 and MCU % ImageInfo.RestartInterval == 0 and MCU ~= TotalMCUs) then
            Buff:Align()

            local ExpextedMarker = 0xFF00 + RSTnMin + (((MCU - RestartInterval) // RestartInterval) % 8)
            local Marker = Buff:ReadBytes(2)

            if (Marker ~= ExpextedMarker) then
                print("Restart Marker error, got marker", Marker, "expected", ExpextedMarker)
                return
            end

            EndOfBandRun = 0
        end

    end
end

function ReadScan(Buff, ImageInfo)
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

    if (Ah == 0) then
        ReadSpectralScan(Buff, Ss, Se, Al, Ah, ComponantsInScan, ComponantParameters, ImageInfo)
    else
        ReadRefinementScan(Buff, Ss, Se, Al, Ah, ComponantsInScan, ComponantParameters, ImageInfo)
    end

end

function ReadRestartInterval(Buff, ImageInfo)
    local Length = Buff:ReadBytes(2)
    ImageInfo.RestartInterval = Buff:ReadBytes(2) --number of MCU in the restart interval
end

function ReadDNL(Buff)
    local Length = Buff:ReadBytes(2)
    local NumLines = Buff:ReadBytes(2)
end

function InterpretMarker(Buff, ImageInfo) --handles calling functions to decode markers
    local Marker = Buff:ReadBytes(1)

    if (Marker == DQT) then
        ReadQuantizationTables(Buff, ImageInfo)
    elseif (Marker == DHT) then
        ReadHuffmanTable(Buff, ImageInfo)
    elseif (Marker == JFIFHeader) then
        ReadJFIFHeader(Buff)
    elseif (Marker == SOF0 or Marker == SOF1 or Marker == SOF2) then
        ReadFrame(Buff, ImageInfo)
    elseif (Marker == SOS) then
        ReadScan(Buff, ImageInfo)
        Buff:Align()
    elseif (Marker == DRI) then
        ReadRestartInterval(Buff, ImageInfo)
    elseif (Marker == EOI) then
        return -1
    elseif (Marker == DAC) then
        print("Arithmetic encoding is not supported")
        os.exit(1)
    elseif (Marker == DNL) then
        ReadDNL(Buff)
        print("DNL currently unsupported")
        os.exit(1)
    elseif (Marker ~= 0) then --0xFF00 is a padding byte
        local Len = Buff:ReadBytes(2) - 2 --skip marker

        if (SOF2 < Marker and Marker <= 0xCF) then
            print("Unsupported frame:", Marker)
            os.exit(1)
        end

        Buff:ReadBytes(Len)
    end

end

function TransformBlocks(ImageInfo)

    local Blocks = ImageInfo.Blocks
    local Pixels = ImageInfo.Pixels
    local X = ImageInfo.X
    local Y = ImageInfo.Y

    for c, info in pairs(ImageInfo.ComponantsInfo) do
        local QuantizationTable = ImageInfo.QuantizationTables[info.QuantizationTableDestination+1]
        local XScale = ImageInfo.HMax // info.HorizontalSamplingFactor
        local YScale = ImageInfo.VMax // info.VerticalSamplingFactor
        local SubImageX = XScale * 8
        local SubImageY = YScale * 8

        for yb = 1, Blocks[c].Y, 1 do
            for xb = 1, Blocks[c].X, 1 do
                --un-zigzag, dequantize and IDCT
                local BlockIndex = (yb - 1) * Blocks[c].X + xb
                local DecodedBlock = Blocks[c][BlockIndex]
                local Block = {}

                for v = 1, 64, 1 do
                    Block[v] = DecodedBlock[ZigZag[v]] * QuantizationTable[ZigZag[v]]
                end

                IDCT(Block)

                local Offset = ImageInfo.SamplePrecision > 0 and 1 << (ImageInfo.SamplePrecision - 1) or 0
                for v = 1, 64, 1 do
                    Block[v] = Block[v] + Offset
                end

                --upsample and map to pixel matrix
                local HorizontalEdge = math.min(SubImageY, (Y - ((yb - 1) * SubImageY)))
                local VerticalEdge = math.min(SubImageX, (X - ((xb - 1) * SubImageX)))
                local ImageYIndex = (yb - 1) * SubImageY * X
                local ImageXIndex = (xb - 1) * SubImageX

                for y = 1, HorizontalEdge, 1 do
                    local BlockYIndex = (y - 1) // YScale

                    for x = 1, VerticalEdge, 1 do
                        local BlockXIndex = (x - 1) // XScale

                        Pixels[c][ImageYIndex + ImageXIndex + 1] = Block[BlockYIndex * 8 + BlockXIndex + 1]

                        ImageXIndex = ImageXIndex + 1
                    end

                    ImageXIndex = ImageXIndex - VerticalEdge
                    ImageYIndex = ImageYIndex + X
                end

            end
        end

    end

end

function DecodeJpeg(FileName)
    local Buff = Buffer.New(FileName)

    if (Buff:ReadBytes(2) ~= 0xFF00 + SOI) then print("inavlid jpg file") return end

    local ImageInfo = {
        X = 0,
        Y = 0,
        Pixels = {},
        QuantizationTables = {{}, {}, {}, {}},
        DCHuffmanCodes = {{}, {}, {}, {}},
        ACHuffmanCodes = {{}, {}, {}, {}},
        ComponantsInfo = {},
        HMax = 0,
        VMax = 0,
        SamplePrecision = 0,
        RestartInterval = 0,
        Blocks = {}
    }

    while (not Buff:IsEmpty()) do
        local Byte = Buff:ReadBytes(1)
        if (Byte == 0xFF) then
            local R = InterpretMarker(Buff, ImageInfo)

            if (R == -1) then
                break
            end

        end
    end

    TransformBlocks(ImageInfo)
    YCbCrToRGB(ImageInfo)

    return ImageInfo
end

return DecodeJpeg
