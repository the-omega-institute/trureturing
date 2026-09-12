/- GID: D5/S3/Arith/Derangements/DerangementTwoAdicValuation
   generality: G
   mirror-B: D5/B/S3/Arith/Derangements/DerangementTwoAdicValuation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Adjacent derangement numbers have opposite parity, giving their exact binary valuation. -/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Derangements.DerangementTwoAdicValuation

-- Utility kind `none`: all declarations are unbounded symbolic theorems, not finite computations.

/-- A derangement number is odd exactly at an even index. -/
theorem numDerangements_odd_iff_even (n : ℕ) :
    Odd (numDerangements n) ↔ Even n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
      simp only [numDerangements_add_two, Nat.odd_mul, Nat.odd_add, hn]
      grind

/-- For every index at least two, the exact binary valuation of the derangement number is
the binary valuation of the preceding index. -/
theorem padicValNat_numDerangements (n : ℕ) (hn : 2 ≤ n) :
    padicValNat 2 (numDerangements n) = padicValNat 2 (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsumOdd : Odd (numDerangements m + numDerangements (m + 1)) := by
    rw [Nat.odd_add, numDerangements_odd_iff_even]
    grind [numDerangements_odd_iff_even (m + 1)]
  have hsum_ne : numDerangements m + numDerangements (m + 1) ≠ 0 := by
    intro hzero
    exact hsumOdd.not_two_dvd_nat (hzero ▸ dvd_zero 2)
  rw [show 2 + m = m + 2 by omega, numDerangements_add_two]
  rw [padicValNat.mul (Nat.succ_ne_zero m) hsum_ne]
  rw [padicValNat.eq_zero_of_not_dvd hsumOdd.not_two_dvd_nat]
  simp

/-- If a derangement number is a natural power, then its exponent divides the binary valuation
of the preceding index. -/
theorem exponent_dvd_padicValNat_sub_one_of_numDerangements_eq_pow
    (n : ℕ) (hn : 2 ≤ n) (b k : ℕ) (hpow : numDerangements n = b ^ k) :
    k ∣ padicValNat 2 (n - 1) := by
  rw [← padicValNat_numDerangements n hn, hpow, padicValNat.pow]
  exact dvd_mul_right k (padicValNat 2 b)

end D5.S3.Arith.Derangements.DerangementTwoAdicValuation
