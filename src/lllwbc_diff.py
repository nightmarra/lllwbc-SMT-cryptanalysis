from lllwbc import LLLWBC
from utils import Utils as U

from time import time
from random import randint

from z3 import *
# z3.set_param('parallel.enable', True)



class LLLWBCDiff(LLLWBC):
    def __init__(self, rounds):
        super().__init__()
        self.rounds = rounds
        self.solver = Solver()
        self.key_vars = [Bool(f'key_{i}') for i in range(128)]

        # declare sbox as a function
        self.sbox_fun = Function('sbox', BitVecSort(4), BitVecSort(4))
        for i, val in enumerate(self.sbox):
            self.solver.add(self.sbox_fun(i) == val)


    # uses the symbolic variable key_vars from the LLLWBCDiff constructor
    def symbolic_key_schedule(self):
        ###--- whitening keys ---###
        kws = [[Bool(f'kw_{i}_{j}') for j in range(64)] for i in range(2)]

        # pre-whitening key – left 64 bits of K
        for i in range(64):
            self.solver.add(kws[0][i] == self.key_vars[i])
    
        # post-whitening key
        self.solver.add(kws[1][0] == self.key_vars[63])
        for i in range(1, 63):
            self.solver.add(kws[1][i] == self.key_vars[i-1])
        self.solver.add(kws[1][63] == Xor(self.key_vars[62], self.key_vars[0]))
    

        ###--- round keys ---###
        krs = [[Bool(f'kr_{r}_{j}') for j in range(32)] for r in range(21)]

        for r in range(0, 20, 2): # rounds 1, 3, ..., 19
            for j in range(4):
                ck_bits = U.byte_to_bit(self.ck[r][j])
                for k in range(8):
                    self.solver.add(
                        krs[r][j*8 + k] == Xor(self.key_vars[64 + j*8 + k], ck_bits[k]))
        
        for r in range(1, 20, 2): # rounds 2, 4, ..., 20
            for j in range(4):
                ck_bits = U.byte_to_bit(self.ck[r][j])
                for k in range(8):
                    self.solver.add(
                        krs[r][j*8 + k] == Xor(self.key_vars[96 + j*8 + k], ck_bits[k]))

        # round 21
        for j in range(4):
            ck_bits = U.byte_to_bit(self.ck[20][j])
            for k in range(8):
                self.solver.add(
                        krs[20][j*8 + k] == Xor(self.key_vars[64 + j*8 + k], ck_bits[k]))

        return kws, krs

   
    def symbolic_f(self, state8):
        u0_nibble = Concat(*[If(bit, BitVecVal(1,1), BitVecVal(0,1)) for bit in state8[:4]])
        u1_nibble = Concat(*[If(bit, BitVecVal(1,1), BitVecVal(0,1)) for bit in state8[4:]])

        u0_s1 = self.sbox_fun(u0_nibble)
        u1_s1 = self.sbox_fun(u1_nibble)

        tu0 = self.symbolic_mul2(u0_s1) ^ self.symbolic_mul3(u1_s1)
        tu1 = u0_s1 ^ u1_s1

        u0_s2 = self.sbox_fun(tu0)
        u1_s2 = self.sbox_fun(tu1)

        result = [False] * 8
        for i in range(4):
            result[i] = Extract(3-i, 3-i, u0_s2) == 1
            result[i+4] = Extract(3-i, 3-i, u1_s2) == 1

        return result


    def symbolic_mul2(self, nibble):
        shifted = (nibble << 1) & 0xf
        condition = (nibble & 0x8) != 0
        return If(condition, shifted ^ 0x3, shifted)
    

    def symbolic_mul3(self, nibble):
        return self.symbolic_mul2(nibble) ^ nibble
    

    def symbolic_p(self, state64):
        perm = [6, 11, 0, 12, 10, 7, 13, 1, 3, 15, 4, 9, 2, 14, 5, 8]
        result = [False] * 64
        
        for i in range(16):
            for j in range(4):
                result[i * 4 + j] = state64[perm[i] * 4 + j]
        
        return result
    

    def symbolic_p_inverse(self, state64):
        inv_perm = [2, 7, 12, 8, 10, 14, 0, 5, 15, 11, 4, 1, 3, 6, 13, 9]
        result = [False] * 64
        
        for i in range(16):
            for j in range(4):
                result[i * 4 + j] = state64[inv_perm[i] * 4 + j]
        
        return result
    

    # uses the number of rounds from the LLLWBCDiff constructor
    def symbolic_encrypt(self, plaintext, kws, krs):
        state = plaintext.copy()
        state = [Xor(state[i], kws[0][i]) for i in range(64)] # pre-whitening

        for r in range(self.rounds):
            current_state = state.copy()

            for j in range(4):
                # 0-7
                left = [Xor(current_state[j*16 + k], krs[r][j*8 + k]) for k in range(8)]
                f_left = self.symbolic_f(left)

                # 8-15
                right = [Xor(current_state[j*16 + 8 + k], f_left[k]) for k in range(8)]
                for k in range(8):
                    current_state[j*16 + 8 + k] = right[k]

            if r < 20:
                if r < 10:
                    current_state = self.symbolic_p(current_state)
                else:
                    current_state = self.symbolic_p_inverse(current_state)

            # update the state for the next round
            state = current_state

        state = [Xor(state[i], kws[1][i]) for i in range(64)] # post-whitening
        return state
    

    # implicitly uses the number of rounds from the constructor for encryption
    def symbolic_verify_path(self, input_diff, output_diff):
        self.solver.push()
        
        input_bits = U.seq_to_bit([(input_diff >> (56 - 8*i)) & 0xff for i in range(8)])
        output_bits = U.seq_to_bit([(output_diff >> (56 - 8*i)) & 0xff for i in range(8)])
        p1 = [Bool(f'p1_{i}') for i in range(64)]
        p2 = [Bool(f'p2_{i}') for i in range(64)]

        # constraint for the input difference
        for i in range(64):
            self.solver.add(Xor(p1[i], p2[i]) == input_bits[i])
        
        # encrypt both plaintexts
        kws, krs = self.symbolic_key_schedule()
        c1 = self.symbolic_encrypt(p1, kws, krs)
        c2 = self.symbolic_encrypt(p2, kws, krs)
        
        # constraint for the output difference
        for i in range(64):
            self.solver.add(Xor(c1[i], c2[i]) == output_bits[i])

        result = self.solver.check()
        model = None
        if result == sat:
            model = self.solver.model()

        self.solver.pop()
        return model, p1, p2, c1, c2



def test_random():
    ROUND_COUNT = 5
    lllwbc_diff = LLLWBCDiff(ROUND_COUNT)

    times = []
    differentials = [(randint(1152921504606846976, 18446744073709551615),
                      randint(1152921504606846976, 18446744073709551615)) 
                      for _ in range(20)]

    for i, (in_diff, out_diff) in enumerate(differentials):
        print(f"\nTesting differential #{i + 1}: "
              f"0x{in_diff:016x} → 0x{out_diff:016x}")

        # check if a differential trail exists
        start = time()
        model, p1, p2, c1, c2 = lllwbc_diff.symbolic_verify_path(in_diff, out_diff)
        duration = time() - start
        times.append(duration)

        if model is None:
            print("✗ Impossible - No key exists that satisfies this differential\n")
            print(f'\nTotal execution time was {round(duration, 3)} seconds.')
            continue
        print("✓ Differential is possible!")

        # extract the key from the model
        key_bits = []
        for i in range(128):
            key_var = lllwbc_diff.key_vars[i]
            key_bits.append(is_true(model.eval(key_var)))

        p1_bits = []
        p2_bits = []
        c1_bits = []
        c2_bits = []
        for i in range(64):
            p1_bits.append(is_true(model.eval(p1[i])))
            p2_bits.append(is_true(model.eval(p2[i])))
            c1_bits.append(is_true(model.eval(c1[i])))
            c2_bits.append(is_true(model.eval(c2[i])))

        # convert to byte sequence and display the key in hex
        key_bytes = U.bit_to_seq(key_bits)
        key_hex = ''.join(f'{b:02x}' for b in key_bytes)
        print(f"Key: {key_hex}")

        p1_bytes = U.bit_to_seq(p1_bits)
        p1_hex = ''.join(f'{b:02x}' for b in p1_bytes)
        print(f"Plaintext 1: {p1_hex}")

        p2_bytes = U.bit_to_seq(p2_bits)
        p2_hex = ''.join(f'{b:02x}' for b in p2_bytes)
        print(f"Plaintext 2: {p2_hex}")

        c1_bytes = U.bit_to_seq(c1_bits)
        c1_hex = ''.join(f'{b:02x}' for b in c1_bytes)
        print(f"Ciphertext 1: {c1_hex}")

        c2_bytes = U.bit_to_seq(c2_bits)
        c2_hex = ''.join(f'{b:02x}' for b in c2_bytes)
        print(f"Ciphertext 2: {c2_hex}")

        print(f'\nTotal execution time was {round(duration, 3)} seconds.')

    print(f'\nAverage time: {sum(times)/20}')
    print(f'\nMin time: {min(times)}')
    print(f'\nMax time: {max(times)}')


def test_multiple():
    ROUND_COUNT = 2
    lllwbc_diff = LLLWBCDiff(ROUND_COUNT)

    differentials = [
            (0x0000000000000001, 0x0000000001000000),
            (0x0000000000000001, 0x0000000000100000),
            (0x0000000100000000, 0x0000010000000000),
            (0x0000001100000000, 0x1000010000000000),
            (0x0000001100000000, 0x40100d009000b010),
            (0x0000001000000000, 0x001000009000b000),
            (0x0000001100000000, 0xb9f81322c4b25947)
    ]

    for i, (in_diff, out_diff) in enumerate(differentials):
        print(f"\nTesting differential #{i + 1}: "
              f"0x{in_diff:016x} → 0x{out_diff:016x}")

        # check if a differential trail exists
        start = time()
        model, p1, p2, c1, c2 = lllwbc_diff.symbolic_verify_path(in_diff, out_diff)
        duration = time() - start

        if model is None:
            print("✗ Impossible - No key exists that satisfies this differential\n")
            print(f'\nTotal execution time was {round(duration, 3)} seconds.')
            continue
        print("✓ Differential is possible!")

        # extract the key from the model
        key_bits = []
        for i in range(128):
            key_var = lllwbc_diff.key_vars[i]
            key_bits.append(is_true(model.eval(key_var)))

        p1_bits = []
        p2_bits = []
        c1_bits = []
        c2_bits = []
        for i in range(64):
            p1_bits.append(is_true(model.eval(p1[i])))
            p2_bits.append(is_true(model.eval(p2[i])))
            c1_bits.append(is_true(model.eval(c1[i])))
            c2_bits.append(is_true(model.eval(c2[i])))

        # convert to byte sequence and display the key in hex
        key_bytes = U.bit_to_seq(key_bits)
        key_hex = ''.join(f'{b:02x}' for b in key_bytes)
        print(f"Key: {key_hex}")

        p1_bytes = U.bit_to_seq(p1_bits)
        p1_hex = ''.join(f'{b:02x}' for b in p1_bytes)
        print(f"Plaintext 1: {p1_hex}")

        p2_bytes = U.bit_to_seq(p2_bits)
        p2_hex = ''.join(f'{b:02x}' for b in p2_bytes)
        print(f"Plaintext 2: {p2_hex}")

        c1_bytes = U.bit_to_seq(c1_bits)
        c1_hex = ''.join(f'{b:02x}' for b in c1_bytes)
        print(f"Ciphertext 1: {c1_hex}")

        c2_bytes = U.bit_to_seq(c2_bits)
        c2_hex = ''.join(f'{b:02x}' for b in c2_bytes)
        print(f"Ciphertext 2: {c2_hex}")

        print(f'\nTotal execution time was {round(duration, 3)} seconds.')


def test_single() -> None:
    ROUND_COUNT = 2
    lllwbc_diff = LLLWBCDiff(ROUND_COUNT)
    in_diff = 0x0000000000000001
    out_diff = 0xc5808abc4233a072

    start = time()
    model, p1, p2, c1, c2 = lllwbc_diff.symbolic_verify_path(in_diff, out_diff)
    duration = time() - start
    
    if model is None:
        print("✗ Impossible - No key exists that satisfies this differential\n")
        return
    print("✓ Differential is possible!")

    # extract the key from the model
    key_bits = []
    for i in range(128):
        key_var = lllwbc_diff.key_vars[i]
        key_bits.append(is_true(model.eval(key_var)))

    p1_bits = []
    p2_bits = []
    c1_bits = []
    c2_bits = []
    for i in range(64):
        p1_bits.append(is_true(model.eval(p1[i])))
        p2_bits.append(is_true(model.eval(p2[i])))
        c1_bits.append(is_true(model.eval(c1[i])))
        c2_bits.append(is_true(model.eval(c2[i])))

    # convert to byte sequence and display the key in hex
    key_bytes = U.bit_to_seq(key_bits)
    key_hex = ''.join(f'{b:02x}' for b in key_bytes)
    print(f"Key: {key_hex}")

    p1_bytes = U.bit_to_seq(p1_bits)
    p1_hex = ''.join(f'{b:02x}' for b in p1_bytes)
    print(f"Plaintext 1: {p1_hex}")

    p2_bytes = U.bit_to_seq(p2_bits)
    p2_hex = ''.join(f'{b:02x}' for b in p2_bytes)
    print(f"Plaintext 2: {p2_hex}")

    c1_bytes = U.bit_to_seq(c1_bits)
    c1_hex = ''.join(f'{b:02x}' for b in c1_bytes)
    print(f"Ciphertext 1: {c1_hex}")

    c2_bytes = U.bit_to_seq(c2_bits)
    c2_hex = ''.join(f'{b:02x}' for b in c2_bytes)
    print(f"Ciphertext 2: {c2_hex}")

    print(f'\nTotal execution time was {round(duration, 3)} seconds.')


def main():
    test_single()

if __name__ == '__main__':
    main()
