from utils import Utils as U


class LLLWBC:
    ck = [[0x13, 0x19, 0x8a, 0x2e],
      [0x03, 0x70, 0x73, 0x44],
      [0xa4, 0x09, 0x38, 0x22],
      [0x29, 0x9f, 0x31, 0xd0],
      [0x08, 0x2e, 0xfa, 0x98],
      [0xec, 0x4e, 0x6c, 0x89],
      [0x45, 0x28, 0x21, 0xe6],
      [0x38, 0xd0, 0x13, 0x77],
      [0xbe, 0x54, 0x66, 0xcf],
      [0x34, 0xe9, 0x0c, 0x6c],
      [0xc9, 0x7c, 0x50, 0xdd],
      [0xf4, 0x45, 0x25, 0xdb],
      [0xbe, 0x54, 0x66, 0xcf],
      [0xf8, 0x7c, 0x3a, 0xc0],
      [0x45, 0x28, 0x21, 0xe6],
      [0x2c, 0xe2, 0x45, 0x3e],
      [0x08, 0x2e, 0xfa, 0x98],
      [0xe9, 0x33, 0x18, 0x67],
      [0xa4, 0x09, 0x38, 0x22],
      [0xc3, 0xdc, 0x5a, 0xf3],
      [0x13, 0x19, 0x8a, 0x2e]]

    sbox = [0x0b, 0x0f, 0x03, 0x02, 0x0a, 0x0c, 0x09, 0x01, 0x06, 0x07, 0x08, 0x00, 0x0e, 0x05, 0x0d, 0x04]


    def __init__(self):
        self.g = 0  
        self.f = []

    # MDS matrix multiplication over GF(2^4)
    def mul2(self, a: int) -> int:
        if a & 0x08:
            return ((a << 1) & 0x0f ^ 0x03)
        return (a << 1)
    
    def mul3(self, a: int) -> int:
        return self.mul2(a) ^ a
    
    
    # generates all the keys
    def lllwbc_key_schedule(self, key: list) -> tuple[
                                                    list[list[bool]], 
                                                    list[list[bool]]
                                                ]:
        ###--- whitening keys ---###
        kws = [[False for _ in range(64)] for _ in range(2)]
    
        # pre-whitening key – left 64 bits of K
        for i in range(64):
            kws[0][i] = key[i]

        # post-whitening key
        kws[1][0] = key[63]
        for i in range(1, 63):
            kws[1][i] = key[i - 1]
        kws[1][63] = key[62] ^ key[0]


        ###--- round keys ---###
        krs = [[False for _ in range(32)] for _ in range(21)]

        for r in range(0, 20, 2): # rounds 1, 3, ..., 19
            for j in range(4):
                ck_bits = U.byte_to_bit(self.ck[r][j])
                for k in range(8):
                    krs[r][j*8 + k] = key[64 + j*8 + k] ^ ck_bits[k]
        
        for r in range(1, 20, 2): # rounds 2, 4, ..., 20
            for j in range(4):
                ck_bits = U.byte_to_bit(self.ck[r][j])
                for k in range(8):
                    krs[r][j*8 + k] = key[96 + j*8 + k] ^ ck_bits[k]

        # round 21
        for j in range(4):
            temp = U.byte_to_bit(self.ck[20][j])
            for k in range(8):
                krs[20][j*8 + k] = key[64 + j*8 + k] ^ temp[k]

        return (kws, krs)

    
    
    # the round function F
    def lllwbc_f(self, state8: list[bool]) -> list[bool]:
        if self.g != 0 and self.g % 4 == 0:
            # U.print_hex_array(self.f, split=2)
            self.f = []
            self.g == 0
        self.f.append(U.bit_to_seq(state8)[0])
        self.g += 1
        
        u0b = [False] * 8
        u1b = [False] * 8

        for i in range(4, 8):
            u0b[i] = state8[i - 4]
            u1b[i] = state8[i]
    
        u0 = self.sbox[U.bit_to_byte(u0b)]
        u1 = self.sbox[U.bit_to_byte(u1b)]
    
        tu0 = self.mul2(u0) ^ self.mul3(u1)
        tu1 = u0 ^ u1
    
        u0 = self.sbox[tu0]
        u1 = self.sbox[tu1]
    
        u0 = u0 << 4 | u1
        return U.byte_to_bit(u0)
    

    # the permutation P
    def lllwbc_p(self, state64: list[bool]) -> list[bool]:
        perm = [6, 11, 0, 12, 10, 7, 13, 1, 3, 15, 4, 9, 2, 14, 5, 8]
        res = [False] * 64
        
        for i in range(16):
            for j in range(4):
                res[i * 4 + j] = state64[perm[i] * 4 + j]
        return res
    
    
    # the inverse permutation P^-1
    def lllwbc_p_inverse(self, state64: list[bool]) -> list[bool]:
        inv_perm = [2, 7, 12, 8, 10, 14, 0, 5, 15, 11, 4, 1, 3, 6, 13, 9]
        res = [False] * 64
    
        for i in range(16):
            for j in range(4):
                res[i * 4 + j] = state64[inv_perm[i] * 4 + j]
        return res
    

    # the round algorithm
    def round_phase(self, 
                    state: list[bool], 
                    krs: list[list[bool]], 
                    round_count: int = 21) -> list[bool]:
        tb8 = [False] * 8

        # i = round number, j = byte level index, k = bit level index
        for i in range(round_count):
            for j in range(4):
                for k in range(8): # 0-7
                    tb8[k] = state[j * 16 + k] ^ krs[i][j * 8 + k]
    
                tb8 = self.lllwbc_f(tb8)
                for k in range(8): # 8-15
                    state[j * 16 + 8 + k] ^= tb8[k]
    
            if i < 20:
                if i < 10:
                    state = self.lllwbc_p(state)
                else:
                    state = self.lllwbc_p_inverse(state)
        return state
    

    # the encryption algorithm
    def lllwbc_encrypt(self, 
                       plain_text: list[bool], 
                       key: list[bool],
                       round_count: int = 21) -> list[bool]:
        if round_count < 0 or round_count > 21:
            raise ValueError("Invalid round count")
    
        kws, krs = self.lllwbc_key_schedule(key)
        state = plain_text.copy()

        state = [(state[i] ^ kws[0][i]) for i in range(64)] # pre-whitening
        state = self.round_phase(state, krs, round_count)   # rounds
        state = [(state[i] ^ kws[1][i]) for i in range(64)] # post-whitening
        return state

    
    # the decryption algorithm
    # equal to encryption with a constant-parameterized key
    # only able to decrypt 21 rounds
    def lllwbc_decrypt(self, 
                       cipher_text: list[bool], 
                       key: list[bool]) -> list[bool]:
        # alpha = 0xc0ac29b7
        a = [0xc0, 0xac, 0x29, 0xb7]
        aB = U.seq_to_bit(a)

        for i in range(32):
            key[96 + i] = key[96 + i] ^ aB[i]
    
        kws, krs = self.lllwbc_key_schedule(key)
        state = cipher_text.copy()
    
        state = [(state[i] ^ kws[1][i]) for i in range(64)] # undo post-whitening
        state = self.round_phase(state, krs, 21)            # rounds
        state = [(state[i] ^ kws[0][i]) for i in range(64)] # undo pre-whitening
        return state
