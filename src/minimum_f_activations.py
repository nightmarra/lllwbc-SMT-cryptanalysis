from lllwbc_diff import LLLWBCDiff
from utils import Utils as U

from z3 import *


class MinimumFActivation(LLLWBCDiff):
    def __init__(self, rounds):
        super().__init__(rounds)

    def bv_byte_to_bit(self, byte):
        assert isinstance(byte, BitVecRef) and byte.size() == 8
        return [Extract(i, i, byte) == BitVecVal(1, 1) for i in reversed(range(8))]

    def seq_to_bit_symbolic(self, byte_list):
        bits = []
        for byte in byte_list:
            if isinstance(byte, int):
                byte = BitVecVal(byte, 8)
            bits.extend(self.bv_byte_to_bit(byte))
        return bits

    def compute_f_ddt(self):
        f_ddt = {}
        max_count = 0

        for input_diff in range(256):  # 8-bit input
            print(input_diff)
            for output_diff in range(256):  # 8-bit output
                count = 0
                for x in range(256):
                    x_bits = U.byte_to_bit(x)
                    xor_bits = U.byte_to_bit(x ^ input_diff)
                    
                    y_bits = self.lllwbc_f(x_bits)
                    y_xor_bits = self.lllwbc_f(xor_bits)
                    
                    y = U.bit_to_byte(y_bits)
                    y_xor = U.bit_to_byte(y_xor_bits)
                    
                    if (y ^ y_xor) == output_diff:
                        count += 1
                if count != 256:
                    max_count = max(count, max_count)

                if count > 0:
                    f_ddt[(input_diff, output_diff)] = count / 256
        
        return (f_ddt, max_count)
    

    # symbolic version of count_active_round_functions() from RFActivation
    def count_active_round_functions_symbolic(self, input_diff):
        self.solver.push()
        for i in range(128):
            self.solver.add(Not(self.key_vars[i])) # force the key to be zeros
        
        input_bits = self.seq_to_bit_symbolic([Extract(63 - 8*i, 56 - 8*i, input_diff) for i in range(8)])
        p1 = [Bool(f'p1_{i}') for i in range(64)]
        p2 = [Bool(f'p2_{i}') for i in range(64)]
        
        # constraint for the input difference
        for i in range(64):
            self.solver.add(Xor(p1[i], p2[i]) == input_bits[i])

        active_f_per_round = []
        active_variables = []
        inter_diffs = []
        _, krs = self.symbolic_key_schedule()
        
        # track states for both plaintexts
        state1 = p1.copy()
        state2 = p2.copy()

        # pre-whitening is not necessary
        for r in range(self.rounds):
            active_vars_in_this_round = []
            round_diffs = []

            current_state1 = state1.copy()
            current_state2 = state2.copy()
            
            for j in range(4):
                # 0-7
                left1 = [Xor(current_state1[j*16 + k], krs[r][j*8 + k]) for k in range(8)]
                left2 = [Xor(current_state2[j*16 + k], krs[r][j*8 + k]) for k in range(8)]
                
                # difference before the round functions
                # a round function is active if any of the bits in this difference is non-zero
                f_input_diff = [Xor(left1[k], left2[k]) for k in range(8)]
                round_diffs.append(f_input_diff)
                f_active = Or(*f_input_diff)

                is_active = Bool(f'active_r{r}_j{j}')
                self.solver.add(is_active == f_active)
                
                active_vars_in_this_round.append(is_active)
                active_variables.append(is_active)

                f_left1 = self.symbolic_f(left1)
                f_left2 = self.symbolic_f(left2)
                
                # 8-15
                right1 = [Xor(current_state1[j*16 + 8 + k], f_left1[k]) for k in range(8)]
                right2 = [Xor(current_state2[j*16 + 8 + k], f_left2[k]) for k in range(8)]
                for k in range(8):
                    current_state1[j*16 + 8 + k] = right1[k]
                    current_state2[j*16 + 8 + k] = right2[k]
            
            inter_diffs.append(round_diffs)

            if r < 20:
                if r < 10:
                    current_state1 = self.symbolic_p(current_state1)
                    current_state2 = self.symbolic_p(current_state2)
                else:
                    current_state1 = self.symbolic_p_inverse(current_state1)
                    current_state2 = self.symbolic_p_inverse(current_state2)
            
            # update the states for the next round
            state1 = current_state1
            state2 = current_state2
            active_f_per_round.append((r + 1, Sum(active_vars_in_this_round)))

        # post-whitening is not necessary
        total = Sum(active_variables)
        return active_f_per_round, total, inter_diffs
    

    # finds the number of mininum active round functions
    def find_minimum_active_fs(self):
        while True:
            try:
                self.solver.pop()
            except Z3Exception:
                break
        self.solver.push()
        for i in range(128):
            self.solver.add(Not(self.key_vars[i]))

        diff = BitVec('input_diff', 64)
        self.solver.add(diff != 0)

        # Count active F's symbolically
        active_f_per_round, active_count, inter_diffs = self.count_active_round_functions_symbolic(diff)

        # Use an optimizer to minimize the number of active F's
        opt = Optimize()
        opt.add(self.solver.assertions())  # Carry over existing constraints
        opt.minimize(active_count)

        # Check if the minimal solution meets the restriction
        if opt.check() == sat:
            model = opt.model()
            input_diff_val = model.eval(diff, model_completion=True).as_long()
            active_val = model.eval(active_count).as_long()

            # Verify the solution concretely (like RFActivation)
            round_counts = []
            for r, count_expr in active_f_per_round:
                round_counts.append((r, model.eval(count_expr).as_long()))

            print(f"✓ Found input diff: 0x{input_diff_val:016x}")
            print(f"Total active F's: {active_val}")
            print("Per-round counts:")
            for r, count in round_counts:
                print(f"  Round {r}: {count} active F's")

            print("\nIntermediate differences:")
            for r in range(self.rounds):
                print(f"Round {r + 1}:")
                diff = []
                for j in range(4):
                    diff.append(U.bit_to_seq([is_true(model.eval(inter_diffs[r][j][k])) for k in range(8)])[0])
                print('  F: ', end='')
                U.print_hex_array(diff, split = 2)

            self.solver.pop()
            return input_diff_val, active_val, round_counts
        else:
            self.solver.pop()
            return None


    # # finds whether, for a given number of rounds, an input diff is possible...
    # # ...such that the number of active F's is less than or equal to restriction
    def find_restricted_round_function_count(self, restriction: int):
        while True:
            try:
                self.solver.pop()
            except Z3Exception:
                break

        self.solver.push()
        for i in range(128):
            self.solver.add(Not(self.key_vars[i]))

        diff = BitVec('input_diff', 64)
        self.solver.add(diff != 0)

        active_f_per_round, active_count, inter_diffs = self.count_active_round_functions_symbolic(diff)
        self.solver.add(active_count <= restriction)

        result = self.solver.check()

        if result == sat:
            model = self.solver.model()
            input_diff_val = model.eval(diff, model_completion=True).as_long()
            active_val = model.eval(active_count).as_long()

            round_counts = []
            for r, count_expr in active_f_per_round:
                round_counts.append((r, model.eval(count_expr).as_long()))

            print(f"✓ Found input diff: 0x{input_diff_val:016x}")
            print(f"Total active F's: {active_val}")
            print("Per-round counts:")
            for r, count in round_counts:
                print(f"  Round {r}: {count} active F's")

            print("\nIntermediate differences:")
            for r in range(self.rounds):
                print(f"Round {r + 1}:")
                diff = []
                for j in range(4):
                    diff.append(U.bit_to_seq([is_true(model.eval(inter_diffs[r][j][k])) for k in range(8)])[0])
                print('  F: ', end='')
                U.print_hex_array(diff, split = 2)

            self.solver.pop()
            return input_diff_val, active_val, round_counts
        else:
            print(f"✗ No differential trail found with ≤ {restriction} active F's")
            self.solver.pop()
            return None
        

def main():
    s = MinimumFActivation(rounds=5)
    s.find_restricted_round_function_count(6)

if __name__ == '__main__':
    main()
