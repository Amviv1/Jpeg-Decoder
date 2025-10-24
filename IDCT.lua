local c1 = math.cos(math.pi / 16) / 2
local c2 = math.cos(2 * math.pi / 16) / 2
local c3 = math.cos(3 * math.pi / 16) / 2
local c4 = math.cos(4 * math.pi / 16) / 2
local c5 = math.cos(5 * math.pi / 16) / 2
local c6 = math.cos(6 * math.pi / 16) / 2
local c7 = math.cos(7 * math.pi / 16) / 2

function IDCT(Data)

    for j = 1, 8, 1 do
        local k11 = (Data[j] + Data[32 + j]) * c4 + c2 * Data[16 + j] + c6 * Data[48 + j]
        local k21 = (Data[j] - Data[32 + j]) * c4 + c6 * Data[16 + j] - c2 * Data[48 + j]
        local k31 = (Data[j] - Data[32 + j]) * c4 - c6 * Data[16 + j] + c2 * Data[48 + j]
        local k41 = (Data[j] + Data[32 + j]) * c4 - c2 * Data[16 + j] - c6 * Data[48 + j]
        local k12 = c1 * Data[8 + j] + c3 * Data[24 + j] + c5 * Data[40 + j] + c7 * Data[56 + j]
        local k22 = c3 * Data[8 + j] - c7 * Data[24 + j] - c1 * Data[40 + j] - c5 * Data[56 + j]
        local k32 = c5 * Data[8 + j] - c1 * Data[24 + j] + c7 * Data[40 + j] + c3 * Data[56 + j]
        local k42 = c7 * Data[8 + j] - c5 * Data[24 + j] + c3 * Data[40 + j] - c1 * Data[56 + j]

        Data[j] = k11 + k12
        Data[8 + j] = k21 + k22
        Data[16 + j] = k31 + k32
        Data[24 + j] = k41 + k42

        Data[56 + j] = k11 - k12
        Data[48 + j] = k21 - k22
        Data[40 + j] = k31 - k32
        Data[32 + j] = k41 - k42
    end

    for i = 0, 56, 8 do --looping over cols to compute the rows of AC^T, starting with row 8
        --indexes are have +1 since i only keeps track of current row offset
        local k11 = (Data[i + 1] + Data[i + 5]) * c4 + c2 * Data[i + 3] + c6 * Data[i + 7]
        local k21 = (Data[i + 1] - Data[i + 5]) * c4 + c6 * Data[i + 3] - c2 * Data[i + 7]
        local k31 = (Data[i + 1] - Data[i + 5]) * c4 - c6 * Data[i + 3] + c2 * Data[i + 7]
        local k41 = (Data[i + 1] + Data[i + 5]) * c4 - c2 * Data[i + 3] - c6 * Data[i + 7]
        local k12 = c1 * Data[i + 2] + c3 * Data[i + 4] + c5 * Data[i + 6] + c7 * Data[i + 8]
        local k22 = c3 * Data[i + 2] - c7 * Data[i + 4] - c1 * Data[i + 6] - c5 * Data[i + 8]
        local k32 = c5 * Data[i + 2] - c1 * Data[i + 4] + c7 * Data[i + 6] + c3 * Data[i + 8]
        local k42 = c7 * Data[i + 2] - c5 * Data[i + 4] + c3 * Data[i + 6] - c1 * Data[i + 8]

        Data[i + 1] = k11 + k12
        Data[i + 2] = k21 + k22
        Data[i + 3] = k31 + k32
        Data[i + 4] = k41 + k42

        Data[i + 8] = k11 - k12
        Data[i + 7] = k21 - k22
        Data[i + 6] = k31 - k32
        Data[i + 5] = k41 - k42
    end

end

return IDCT