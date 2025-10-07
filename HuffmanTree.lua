local HuffmanTree = {
    Root = {}
}

HuffmanTree.__index = HuffmanTree

function HuffmanTree.New()
    local NewTree = setmetatable({}, HuffmanTree)
    NewTree.Root = {}
    return NewTree
end

function HuffmanTree:AddCode(Code, Bits, Value)

    local CurrentTable = self.Root

    for i = 1, Bits, 1 do
        local Bit = (Code >> (Bits - i)) & 1

        if (CurrentTable[Bit] == nil) then
            CurrentTable[Bit] = {}
        end

        CurrentTable = CurrentTable[Bit]
    end

    if (CurrentTable[0] ~= nil or CurrentTable[1] ~= nil or CurrentTable.Value ~= nil) then
        error("Attempt to add code that is a prefix of an already existing code", 1)
    end

    CurrentTable.Value = Value
end

function HuffmanTree:Index(Code, Bits)
    local CurrentTable = self.Root

    for i = 1, Bits, 1 do
        CurrentTable = CurrentTable[(Code >> (Bits - i)) & 1]
    end

    return CurrentTable.Value
end

return HuffmanTree