/- GID: D5/S1/Recurrence/Parity/A385590
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/A385590
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The Fibonacci triangle of OEIS A385590 satisfies its alternating binomial sum. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFib

namespace D5.S1.Recurrence.Parity.A385590

open Finset

/-- The integer-valued triangle in OEIS A385590, using its lower Fibonacci inverse. -/
def T (n k : ℕ) : ℤ :=
  let i := Nat.greatestFib n
  (Nat.fib (i - 1) : ℤ) ^ 2 + 1 - ((i - 1) % 2 : ℕ) +
    ((n : ℤ) - Nat.fib i) * Nat.fib (i - 2) +
    ((k : ℤ) - 1) * Nat.fib (i - 1)

/-- The inverse used in `T` is the unique index specified in the OEIS definition. -/
theorem row_index_spec (n : ℕ) (hn : 1 ≤ n) :
    1 < Nat.greatestFib n ∧ Nat.fib (Nat.greatestFib n) ≤ n ∧
      n < Nat.fib (Nat.greatestFib n + 1) ∧
      ∀ i, 1 < i → Nat.fib i ≤ n → n < Nat.fib (i + 1) →
        i = Nat.greatestFib n := by
  have htwo : 2 ≤ Nat.greatestFib n := Nat.le_greatestFib.mpr (by simpa using hn)
  refine ⟨by omega, Nat.fib_greatestFib_le n, Nat.lt_fib_greatestFib_add_one n, ?_⟩
  intro i _ hlo hhi
  have hi := Nat.le_greatestFib.mpr hlo
  have hj := Nat.greatestFib_lt.mpr hhi
  omega

/-- For a fixed row, the displayed constant and slope give its affine formula. -/
theorem row_affine (n k i : ℕ) (hi : i = Nat.greatestFib n) :
    T n k =
      ((Nat.fib (i - 1) : ℤ) ^ 2 + 1 - ((i - 1) % 2 : ℕ) +
        ((n : ℤ) - Nat.fib i) * Nat.fib (i - 2)) +
      ((k : ℤ) - 1) * (Nat.fib (i - 1) : ℤ) := by
  subst i
  rfl

private theorem weighted_sum_zero (m : ℕ) (hm : 2 ≤ m) :
    (∑ j ∈ range (m + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * j) = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    Nat.cast_zero, mul_zero, add_zero]
  have hc (j : ℕ) :
      ((2 + r).choose (j + 1) : ℤ) * (j + 1) =
        (2 + r : ℤ) * ((1 + r).choose j : ℤ) := by
    have h := (Nat.add_one_mul_choose_eq (1 + r) j).symm
    rw [show 1 + r + 1 = 2 + r by omega] at h
    exact_mod_cast h
  have hs := Int.alternating_sum_range_choose_of_ne (n := 1 + r) (by omega)
  calc
    (∑ j ∈ range (2 + r), (-1 : ℤ) ^ (j + 1) *
        ((2 + r).choose (j + 1) : ℤ) * (j + 1)) =
        -(2 + r : ℤ) * ∑ j ∈ range (2 + r),
          (-1 : ℤ) ^ j * ((1 + r).choose j : ℤ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [pow_succ, mul_assoc, hc]
      ring
    _ = 0 := by
      rw [show 2 + r = 1 + r + 1 by omega, hs, mul_zero]

private theorem affine_sum_zero (m : ℕ) (hm : 2 ≤ m) (A B : ℤ) :
    (∑ j ∈ range (m + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) *
      (A + j * B)) = 0 := by
  simp_rw [mul_add, ← mul_assoc]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul,
    Int.alternating_sum_range_choose_of_ne (by omega), weighted_sum_zero m hm]
  ring

/-- The alternating binomial sum conjectured in OEIS A385590, for every positive row. -/
theorem alternating_binomial_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Icc 1 n, (-1 : ℤ) ^ k * ((n - 1).choose (k - 1) : ℤ) * T n k) =
      if n < 3 then (-1 : ℤ) ^ n else 0 := by
  by_cases hsmall : n < 3
  · interval_cases n <;> norm_num [T, Nat.greatestFib, Nat.findGreatest,
      show Icc 1 2 = {1, 2} by decide]
  · rw [if_neg hsmall, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
    have hn' : n = (n - 1) + 1 := by omega
    let i := Nat.greatestFib n
    let A : ℤ := (Nat.fib (i - 1) : ℤ) ^ 2 + 1 - ((i - 1) % 2 : ℕ) +
      ((n : ℤ) - Nat.fib i) * Nat.fib (i - 2)
    let B : ℤ := Nat.fib (i - 1)
    calc
      (∑ j ∈ range n, (-1 : ℤ) ^ (1 + j) * ((n - 1).choose j : ℤ) * T n (1 + j)) =
          -(∑ j ∈ range n, (-1 : ℤ) ^ j * ((n - 1).choose j : ℤ) *
            (A + j * B)) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro j _
        rw [row_affine n (1 + j) i rfl]
        simp only [Nat.cast_add, Nat.cast_one, pow_add, pow_one]
        dsimp only [A, B]
        ring
      _ = 0 := by
        conv_lhs => arg 1; rw [hn']
        simpa using congrArg Neg.neg (affine_sum_zero (n - 1) (by omega) A B)

#print axioms row_index_spec
#print axioms row_affine
#print axioms alternating_binomial_sum

end D5.S1.Recurrence.Parity.A385590
