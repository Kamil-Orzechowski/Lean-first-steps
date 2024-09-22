def arith_sum : Nat → Nat
| 0 => 0
| n + 1 => n + 1 + arith_sum n

def arith_formula (n : Nat) : Nat := n * (n + 1) / 2

def aux (n : Nat) : (n + 1) * (n + 1 + 1) = (n + 1) * n + (n + 1) * 2 :=
  by rw[Nat.add_assoc, Nat.mul_add]

theorem arith_eq (n : Nat) : arith_formula n = arith_sum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw[arith_formula, arith_sum, ←ih, arith_formula, Nat.add_assoc, Nat.mul_add, Nat.add_mul_div_right]
    rw[Nat.add_comm, Nat.mul_comm]
    exact Nat.zero_lt_two

  #check Nat.succ_eq_add_one
