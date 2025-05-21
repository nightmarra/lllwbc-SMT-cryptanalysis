from lllwbc_diff import LLLWBCDiff
from utils import Utils as U

from z3 import *


# the round function can be thought of as a non-linear 8-bit sbox
class RFActivation(LLLWBCDiff):
    def __init__(self, rounds):
        super().__init__(rounds)
        self.rounds = rounds
        
    
    # counts how many F's are active during each round
    def count_active_round_functions(self, input_diff):
        self.solver.push()
        for i in range(128):
            self.solver.add(Not(self.key_vars[i]))  # force the key to be zeros

        input_bits = U.seq_to_bit([(input_diff >> (56 - 8*i)) & 0xff for i in range(8)])
        p1 = [Bool(f'p1_{i}') for i in range(64)]
        p2 = [Bool(f'p2_{i}') for i in range(64)]

        # constraint for the input difference
        for i in range(64):
            self.solver.add(Xor(p1[i], p2[i]) == input_bits[i])

        active_f_per_round = []
        _, krs = self.symbolic_key_schedule()

        # track states for both plaintexts
        state1 = p1.copy()
        state2 = p2.copy()

        # intermediate differences
        inter_diffs = []

        for r in range(self.rounds):
            active_in_this_round = 0
            current_state1 = state1.copy()
            current_state2 = state2.copy()
            round_diffs = []

            for j in range(4):
                # 0-7
                left1 = [Xor(current_state1[j*16 + k], krs[r][j*8 + k]) for k in range(8)]
                left2 = [Xor(current_state2[j*16 + k], krs[r][j*8 + k]) for k in range(8)]

                # difference before the round functions
                f_input_diff = [Xor(left1[k], left2[k]) for k in range(8)]
                round_diffs.append(f_input_diff)

                f_active = Or(*f_input_diff)
                is_active = Bool(f'active_r{r}_j{j}')
                self.solver.add(is_active == f_active)
                active_in_this_round += If(is_active, 1, 0)

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

            state1 = current_state1
            state2 = current_state2
            active_f_per_round.append((r + 1, active_in_this_round))

        result = self.solver.check()
        round_counts = []

        if result == sat:
            model = self.solver.model()

            print("\nIntermediate differences:")
            for r in range(self.rounds):
                print(f"Round {r + 1}:")
                diff = []
                for j in range(4):
                    diff.append(U.bit_to_seq([is_true(model.eval(inter_diffs[r][j][k])) for k in range(8)])[0])
                print('  F: ', end='')
                U.print_hex_array(diff, split = 2)

            for round_num, count_expr in active_f_per_round:
                round_counts.append((round_num, model.eval(count_expr).as_long()))
        else:
            print("No valid differential path found")

        self.solver.pop()
        return round_counts

    
    # returns the output of count_active_round_functions in a prettier format
    def analyze_differential_path(self, input_diff):
        active_counts = self.count_active_round_functions(input_diff)

        if active_counts is None:
            print(f"No valid differential path found for input difference: 0x{input_diff:016x}")
            return None
        total_active = sum(count for _, count in active_counts)
        
        print(f"Analysis for input difference: 0x{input_diff:016x}")
        print(f"Number of rounds: {self.rounds}")
        print("Active F's per round:")
        for round_num, count in active_counts:
            print(f"  Round {round_num}: {count} active F's")
        print(f"Total active F's: {total_active}")

        return total_active
    
    
def test():
    s = RFActivation(rounds=21)
    print(s.count_active_round_functions(0x0000000000000001))
   

def main():
    test()

if __name__ == '__main__':
    main()
