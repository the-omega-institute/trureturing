import Mathlib.Data.Nat.Fib.Basic

/-- 命题 342.2, first clause: the chapter row G n = fib (n + 2) is a positive integer and strictly increasing. -/
theorem zeckendorf_row_positive_increasing :
    (∀ n : ℕ, 0 < Nat.fib (n + 2)) ∧ ∀ n : ℕ, Nat.fib (n + 2) < Nat.fib (n + 3) :=
  ⟨fun n => Nat.fib_pos.mpr (by omega), fun n => Nat.fib_add_two_strictMono (Nat.lt_succ_self n)⟩

#print axioms zeckendorf_row_positive_increasing
