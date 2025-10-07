local BitBuffer = {
    Bytes = {},
    CurrentByte = 1,
    Bit = 0
}

BitBuffer.__index = BitBuffer

function BitBuffer.New(FileName)
    local Buffer = setmetatable({}, BitBuffer)
    local File = io.open(FileName, "rb")
    local Data = File:read("a")

    io.close(File)

    for i = 1, #Data, 1 do -- can optimize by just keeping the file and getting next byte when needed
        Buffer.Bytes[i] = string.unpack(">I1", Data, i)
    end

    return Buffer
end

function BitBuffer:ReadLBit()
    local Bit = (self.Bytes[self.CurrentByte] >> (7 - self.Bit)) & 1
    self.Bit = self.Bit + 1

    if (self.Bit > 7) then
        self.CurrentByte = self.CurrentByte + 1
        self.Bit = 0

        if (self.Bytes[self.CurrentByte] == 0x00 and self.Bytes[self.CurrentByte-1] == 0xFF) then
            self.CurrentByte = self.CurrentByte + 1
        elseif (self.Bytes[self.CurrentByte-1] == 0xFF) then
            error("Unexpected marker in entropy stream: "..tostring(self.Bytes[self.CurrentByte]), 1)
        end
    end

    return Bit
end

function BitBuffer:ReadLBits(NumBits)
    local Bits = 0

    for i = 1, NumBits, 1 do
        Bits = (Bits << 1) | self:ReadLBit()
    end

    return Bits
end

function BitBuffer:ReadLBytes(NumBytes)
    if (self.Bit ~= 0) then
        error("Attempt to read misaligned byte(s)", 1)
    end

    local Bytes = 0

    for i = 1, NumBytes, 1 do
        Bytes = (Bytes << 8) | self.Bytes[self.CurrentByte]
        self.CurrentByte = self.CurrentByte + 1
    end

    return Bytes
end

function BitBuffer:ShowNext()
    return self.Bytes[self.CurrentByte + 1]
end

function BitBuffer:Align()
    if (self.Bit == 0) then return end

    self.Bit = 0
    self.CurrentByte = self.CurrentByte + 1
end

function BitBuffer:IsEmpty()
    return #self.Bytes < self.CurrentByte
end

return BitBuffer