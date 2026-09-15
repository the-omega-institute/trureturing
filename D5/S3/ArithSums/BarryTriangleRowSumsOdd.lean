/- GID: D5/S3/ArithSums/BarryTriangleRowSumsOdd
   generality: I
   mirror-B: D5/B/S3/ArithSums/BarryTriangleRowSumsOdd
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius]
   utility: none
   digest: OEIS A105595: every row sum of the A105594 triangle is odd. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.BarryTriangleRowSumsOdd

/-- The entry `T(n, k)` from the formula in OEIS A105594. -/
def rowEntry (n k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (n + 1),
      Int.natAbs (ArithmeticFunction.moebius (Nat.choose n j)) *
        (Nat.choose j k % 2)) % 2

/-- The row sum `a(n)` from the formula in OEIS A105595. -/
def rowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), rowEntry n k

/-- Every row sum in OEIS A105595 is odd. -/
theorem result : ∀ n : ℕ, Odd (rowSum n) := by
  intro n
  rw [Nat.odd_iff]
  have hchoose (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (∑ k ∈ Finset.range (n + 1), Nat.choose j k) = 2 ^ j := by
    rw [← Nat.sum_range_choose j]
    symm
    apply Finset.sum_subset (Finset.range_mono (by simpa using hj))
    intro k hk hkj
    simp only [Finset.mem_range] at hk hkj
    exact Nat.choose_eq_zero_of_lt (by omega)
  have hcast : (rowSum n : ZMod 2) = 1 := by
    simp only [rowSum, rowEntry, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      (∑ j ∈ Finset.range (n + 1),
          (Int.natAbs (ArithmeticFunction.moebius (Nat.choose n j)) : ZMod 2) *
            ∑ k ∈ Finset.range (n + 1), (Nat.choose j k : ZMod 2)) =
          ∑ j ∈ Finset.range (n + 1),
            (Int.natAbs (ArithmeticFunction.moebius (Nat.choose n j)) : ZMod 2) *
              (2 ^ j : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Nat.cast_sum, hchoose j hj, Nat.cast_pow, Nat.cast_ofNat]
      _ = 1 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro j hj hj0
          simp [show (2 : ZMod 2) = 0 by decide, hj0]
        · simp
  exact (ZMod.natCast_eq_natCast_iff' (rowSum n) 1 2).mp (by simpa using hcast)

#print axioms rowEntry
#print axioms rowSum
#print axioms result

end D5.S3.ArithSums.BarryTriangleRowSumsOdd
