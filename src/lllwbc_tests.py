from lllwbc import LLLWBC
from utils import Utils as U

from z3 import *


class Tests:
    def __init__(self):
        pass

    # takes a plaintext and a key and returns the result of encryption
    # optionally decrypts if round_count is 21
    def encryption_wrapper(self, 
                           l: LLLWBC,
                           plaintext: list[int], 
                           key: list[int],
                           round_count: int = 21
                          ) -> None:
        print("=" * 40)

        print('\nEncrypting plaintext: 0x', end='')
        U.print_hex_array(plaintext)

        print('Using key: 0x', end='')
        U.print_hex_array(key)

        print(f'Round count: {round_count}')

        pB = U.seq_to_bit(plaintext)
        kB = U.seq_to_bit(key)
        cB = l.lllwbc_encrypt(pB, kB, round_count)

        print('\nCiphertext:')
        print('0x', end='')
        U.print_hex_array(U.bit_to_seq(cB))

        if round_count == 21:
            oB = l.lllwbc_decrypt(cB, kB)
            print('\nDecrypted plaintext:')
            print('0x', end='')

            decrypted = U.bit_to_seq(oB)
            U.print_hex_array(decrypted)

            if decrypted == plaintext:
                print('\033[92m' + '✓ CORRECT.' + '\x1b[0m')
            else:
                print('\033[91m' + '✗ INCORRECT, DECRYPTED != ORIGINAL!' + '\x1b[0m')

        print(f'\n{"=" * 40}')


    # returns a differential of two plaintexts
    def differential(self,
                     P1: list[int], 
                     P2: list[int]):
        p1B = U.seq_to_bit(P1)
        p2B = U.seq_to_bit(P2)

        res = []
        for i in range(len(p1B)):
            res.append(p1B[i] ^ p2B[i])
        return U.bit_to_seq(res)


    # returns a differential of two ciphertexts
    def enc_differential(self,
                         l: LLLWBC,
                         P1: list[int], 
                         P2: list[int], 
                         key: list[int], 
                         round_count: int = 21):
        p1B = U.seq_to_bit(P1)
        p2B = U.seq_to_bit(P2)
        kB = U.seq_to_bit(key)

        c1B = l.lllwbc_encrypt(p1B, kB, round_count)
        c2B = l.lllwbc_encrypt(p2B, kB, round_count)

        res = []
        for i in range(len(c1B)):
            res.append(c1B[i] ^ c2B[i])
        return U.bit_to_seq(res)


    # finds all (x, x') such that x ^ x' = Δx and sbox(x) ^ sbox(x') = Δy
    def find_sbox_pairs(self, l: LLLWBC, delta_x: int, delta_y: int):
        s = Solver()
        x = BitVec('x', 4)
        x_prime = BitVec('x_prime', 4)
        y = BitVec('y', 4)
        y_prime = BitVec('y_prime', 4)

        sbox_z3 = Function('sbox', BitVecSort(4), BitVecSort(4))
        for i, val in enumerate(l.sbox):
            s.add(sbox_z3(i) == val)

        # constraints
        s.add(x ^ x_prime == delta_x)
        s.add(y == sbox_z3(x))
        s.add(y_prime == sbox_z3(x_prime))
        s.add(y ^ y_prime == delta_y)

        solutions = []
        while s.check() == sat: # find all solutions
            m = s.model()
            x_val = m.eval(x).as_long()
            x_prime_val = m.eval(x_prime).as_long()
            solutions.append((x_val, x_prime_val))

            # do not return existing solution anymore
            s.add(Or(x != x_val, x_prime != x_prime_val)) 

        return solutions


    # computes DDT with the usual method
    def compute_ddt(self, l: LLLWBC) -> list[list[int]]:
        ddt = [[0] * (16) for _ in range(16)]   # 16 values for 4-bit sbox

        for x in range(16):
            for y in range(16):
                delta_n = x ^ y                 # no sbox
                delta_s = l.sbox[x] ^ l.sbox[y] # sbox
                ddt[delta_n][delta_s] += 1

        return ddt


    # computes DDT using an SMT solver
    def compute_ddt_smt(self, l: LLLWBC) -> list[list[int]]:
        ddt = [[0] * (16) for _ in range(16)]   # 16 values for 4-bit sbox

        for delta_x in range(16):
            for delta_y in range(16):
                solutions = self.find_sbox_pairs(l, delta_x, delta_y)
                ddt[delta_x][delta_y] = len(solutions)

        return ddt


    # prints the DDT in a nice format
    def print_ddt(self, ddt: list[list[int]], from_smt: bool) -> None:
        if from_smt:
            print("\nDDT computed with an SMT solver (rows = Δx, columns = Δy):")
            for delta_x in range(16):
                print(f"Δx = {delta_x:01X}: {ddt[delta_x]}")
        else:
            print("\nDDT (rows = Δx, columns = Δy):")
            for delta_x in range(16):
                print(f"Δx = {delta_x:01X}: {ddt[delta_x]}")


    # prints an analysis of the DDT
    def print_detailed_ddt_analysis(self, ddt: list[list[int]]) -> None:
        total_entries = 0
        best_differentials = []

        print("\nDDT analysis summary:")
        print("=" * 40)

        for dx in range(1, len(ddt)):  # dx = 0 is not considered
            for dy in range(len(ddt[dx])):
                count = ddt[dx][dy]
                if count > 0:
                    total_entries += 1
                    if count == 4:
                        best_differentials.append((dx, dy, count))

        print(f"Total non-zero differential entries: {total_entries}")
        print(f"Number of optimal differentials (count = 4): {len(best_differentials)}")

        print("\nOptimal differentials:")
        for dx, dy, count in best_differentials:
            print(f"  {dx:2X} ->{dy:2X} (count: {count}, prob: {count / 16})")

        # check uniformity, average probability has to be 1/16 = 0.0625
        avg_prob = sum(sum(row[1:]) for row in ddt[1:]) / (15 * 16)  # dx = 0 is not considered
        print(f"\nAverage differential probability: {avg_prob/16}")
        print("=" * 40)



def playground_1():
    l = LLLWBC()
    t = Tests()
    print('\n')

    ROUND_COUNT = 6
    P1 = [0x00, 0x00, 0xb9, 0x00, 0x00, 0x00, 0x00, 0x00]
    P2 = [0x00, 0x00, 0xb9, 0x00, 0x00, 0x00, 0x00, 0x01]
    key = [0x20, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

    t.encryption_wrapper(l, P1, key, ROUND_COUNT)
    t.encryption_wrapper(l, P2, key, ROUND_COUNT)

    U.print_hex_array(t.differential(P1, P2), split = 2)
    U.print_hex_array(t.enc_differential(l, P1, P2, key, ROUND_COUNT), split = 2)

   
def playground_2():
    l = LLLWBC()
    t = Tests()

    delta_x = 0xe
    delta_y = 0x6
    print(f"Pairs for Δx = {delta_x}, Δy = {delta_y}:", t.find_sbox_pairs(l, delta_x, delta_y))

    t.print_detailed_ddt_analysis(t.compute_ddt_smt(l))
    t.print_ddt(t.compute_ddt_smt(l), True)


def playground_3():
    l = LLLWBC()
    t = Tests()
    
    ROUND_COUNT = 21
    P1 = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    P2 = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]
    key = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

    t.encryption_wrapper(l, P1, key, ROUND_COUNT)
    t.encryption_wrapper(l, P2, key, ROUND_COUNT)

    U.print_hex_array(t.differential(P1, P2), split = 2)
    U.print_hex_array(t.enc_differential(l, P1, P2, key, ROUND_COUNT), split = 2)


def playground_4():
    l = LLLWBC()
    t = Tests()
    
    ROUND_COUNT = 5
    P1 = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]
    key = [0x00, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10]

    t.encryption_wrapper(l, P1, key, ROUND_COUNT)



def main():
    playground_3()
    pass

if __name__ == '__main__':
    main()
