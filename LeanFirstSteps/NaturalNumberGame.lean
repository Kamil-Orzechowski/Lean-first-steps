set_option linter.unusedVariables false

example (x y z : Nat)(h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by exact h1

example (x y : Nat) (h : 0 + x = 0 + y + 2) : x = y + 2 :=
by
repeat rw[Nat.zero_add] at h
exact h

theorem impl (x y : Nat) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 :=
h2 h1

#check impl

example (x y : Nat) (h : x + 1 = y + 1) : x = y := by
repeat rw[← Nat.succ_eq_add_one] at h
exact Nat.succ_inj'.mp h
