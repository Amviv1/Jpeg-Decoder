local BitBuffer = {
    Bytes = "",
    Size = 0,
    ByteIndex = 0,
    CurrentByte = 0,
    Bit = 0
}

BitBuffer.__index = BitBuffer

function BitBuffer.New(FileName)
    local Buffer = setmetatable({}, BitBuffer)
    local File = io.open(FileName, "rb")

    Buffer.Bytes = File:read("a")
    Buffer.Size = #Buffer.Bytes

    io.close(File)

    return Buffer
end

function BitBuffer:ReadBit()

    if (self.Bit == 0) then
        self.ByteIndex = self.ByteIndex + 1
        self.Bit = 0
        local NextByte = string.unpack(">I1", self.Bytes, self.ByteIndex)

        if (NextByte == 0x00 and self.CurrentByte == 0xFF) then
            self.ByteIndex = self.ByteIndex + 1
            NextByte = string.unpack(">I1", self.Bytes, self.ByteIndex)
        elseif (self.CurrentByte == 0xFF) then
            error("Unexpected marker in entropy stream: "..tostring(NextByte), 1)
        end

        self.CurrentByte = NextByte
    end

    local Bit = (self.CurrentByte >> (7 - self.Bit)) & 1
    self.Bit = (self.Bit + 1) & 0x7

    return Bit
end

function BitBuffer:ReadBits(NumBits)
    local Bits = 0

    for i = 1, NumBits, 1 do
        Bits = (Bits << 1) | self:ReadBit()
    end

    return Bits
end

function BitBuffer:ReadBytes(NumBytes)
    if (self.Bit ~= 0) then
        self:Align()
    end

    local Bytes = 0

    for i = 1, NumBytes, 1 do
        self.ByteIndex = self.ByteIndex + 1
        self.CurrentByte = string.unpack(">I1", self.Bytes, self.ByteIndex)
        Bytes = (Bytes << 8) | self.CurrentByte
    end

    return Bytes
end

function BitBuffer:Align()
    self.Bit = 0
end

function BitBuffer:IsEmpty()
    return self.Size <= self.ByteIndex
end

return BitBuffer
