class Utils:
    # prints an array of numbers in a hexadecimal format
    # use split = n to get a space after n bytes
    # for example: abcdefabcdef0987
    # split = 2:   abcd efab cdef 0987
    @staticmethod
    def print_hex_array(arr: list[int], split: None | int = None) -> None:
        s = 0
        for num in arr:
            s += 1
            to_print = str(hex(num))[2:]
            if len(to_print) == 1:
                to_print = '0' + to_print
            print(to_print, end='')
            if s == split:
                print(' ', end='')
                s = 0
        print()

    # converts a sequence of bits to a number
    @staticmethod
    def bit_to_byte(bits: list[bool]) -> int:
        res = 0
        for i in range(8):
            if bits[i]:
                res += 1 << (7 - i)
        return res
    
    # converts a number to a sequence of bits
    @staticmethod
    def byte_to_bit(bytes: int) -> list[bool]:
        res = [False] * 8
        for i in range(7, -1, -1):
            if (bytes & 0x01):
                res[i] = True
            bytes >>= 1
        return res

    # converts a sequence of numbers (used for hex) to a sequence of bits
    @staticmethod
    def seq_to_bit(seq: list[int]) -> list[bool]:
        res = [False] * (8 * len(seq))
        for i in range(len(seq)):
            temp = Utils.byte_to_bit(seq[i])
            for j in range(8):
                res[8*i + j] = temp[j]
        return res

    # converts a sequence of bits to a sequence of numbers
    @staticmethod
    def bit_to_seq(bits: list[bool]) -> list[int]:
        res = [0] * (len(bits) // 8)
        for i in range(len(res)):
            res[i] = Utils.bit_to_byte(bits[(8*i):(8*i+8)])
        return res
