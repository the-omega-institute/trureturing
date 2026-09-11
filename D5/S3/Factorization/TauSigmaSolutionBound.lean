/- GID: D5/S3/Factorization/TauSigmaSolutionBound
   generality: G
   mirror-B: D5/B/S3/Factorization/TauSigmaSolutionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every positive tau-sigma product fixed point is less than three to the thirteenth. -/

import D5.S3.Factorization.TauSigmaPowerBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.TauSigmaSolutionBound

open ArithmeticFunction
open D5.S3.Factorization.TauSigmaPowerBounds

/-!
This module proves only the bound m < 3^13 for positive solutions of the equality in
Ivan N. Ianakiev's OEIS A336687 comment (2020-08-06). It does NOT prove the A336687
conjecture. The finite classification below is an explicit, unfulfilled hypothesis.
No exhaustive search result or axiom is installed in the environment.

The numerical premises of the bound are the two proved uniform estimates. The conditional
classification is a companion consumer of that bound; its finite hypothesis remains open.
-/

/-- Every positive solution of the tau-sigma product equation lies below 3^13. -/
theorem tau_sigma_solution_lt (m : ℕ) (hm : 1 ≤ m)
    (heq : sigma 0 (sigma 1 m) * sigma 1 (sigma 0 m) = m) : m < 3 ^ 13 := by
  have ha : sigma 0 (sigma 1 m) ^ 16 ≤ 3 * 9 ^ 16 * m ^ 5 := by
    calc
      _ = (sigma 0 (sigma 1 m) ^ 4) ^ 4 := by ring
      _ ≤ (9 ^ 4 * sigma 1 m) ^ 4 :=
        Nat.pow_le_pow_left (tau_pow_four_le (sigma 1 m)) 4
      _ = 9 ^ 16 * sigma 1 m ^ 4 := by ring
      _ ≤ 9 ^ 16 * (3 * m ^ 5) := Nat.mul_le_mul_left _ (sigma_pow_four_le m)
      _ = 3 * 9 ^ 16 * m ^ 5 := by ring
  have hb : sigma 1 (sigma 0 m) ^ 16 ≤ 3 ^ 4 * 9 ^ 20 * m ^ 5 := by
    calc
      _ = (sigma 1 (sigma 0 m) ^ 4) ^ 4 := by ring
      _ ≤ (3 * sigma 0 m ^ 5) ^ 4 :=
        Nat.pow_le_pow_left (sigma_pow_four_le (sigma 0 m)) 4
      _ = 3 ^ 4 * (sigma 0 m ^ 4) ^ 5 := by ring
      _ ≤ 3 ^ 4 * (9 ^ 4 * m) ^ 5 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (tau_pow_four_le m) 5)
      _ = 3 ^ 4 * 9 ^ 20 * m ^ 5 := by ring
  have h16 : m ^ 16 ≤ 3 ^ 77 * m ^ 10 := by
    calc
      m ^ 16 = sigma 0 (sigma 1 m) ^ 16 * sigma 1 (sigma 0 m) ^ 16 := by
        rw [← mul_pow, heq]
      _ ≤ (3 * 9 ^ 16 * m ^ 5) * (3 ^ 4 * 9 ^ 20 * m ^ 5) := Nat.mul_le_mul ha hb
      _ = 3 ^ 77 * m ^ 10 := by ring
  have h6 : m ^ 6 ≤ 3 ^ 77 := by
    have hcancel : m ^ 6 * m ^ 10 ≤ 3 ^ 77 * m ^ 10 := by
      simpa only [← pow_add] using h16
    exact Nat.le_of_mul_le_mul_right hcancel (by positivity)
  exact lt_of_pow_lt_pow_left' 6 (h6.trans_lt (by norm_num))

/-- Conditional classification. The finite-exhaustion premise has NOT been proved here. -/
theorem tau_sigma_product_eq_self_iff_of_finite
    (hfinite : ∀ n : ℕ, 1 ≤ n → n < 3 ^ 13 →
      (sigma 0 (sigma 1 n) * sigma 1 (sigma 0 n) = n ↔
        n = 1 ∨ n = 468 ∨ n = 3240))
    (m : ℕ) (hm : 1 ≤ m) :
    sigma 0 (sigma 1 m) * sigma 1 (sigma 0 m) = m ↔
      m = 1 ∨ m = 468 ∨ m = 3240 := by
  constructor
  · intro heq
    exact (hfinite m hm (tau_sigma_solution_lt m hm heq)).mp heq
  · intro hsol
    have hlt : m < 3 ^ 13 := by
      rcases hsol with rfl | rfl | rfl <;> norm_num
    exact (hfinite m hm hlt).mpr hsol

#print axioms tau_sigma_solution_lt
#print axioms tau_sigma_product_eq_self_iff_of_finite

end D5.S3.Factorization.TauSigmaSolutionBound
