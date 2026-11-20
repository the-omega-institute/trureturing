/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff]
   utility: none
   digest: Morgan–Voyce P_m has coefficients C(m+k,2k) + 2C(m+k,2k+1), the sheared v-columns. -/

import D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients

/-! The Morgan–Voyce shear of the affine polynomial pair coefficients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairMorganVoyceShear

open Polynomial D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
noncomputable section

/-- The Morgan–Voyce polynomials `P_0 = 1`, `P_1 = 3 + x`, `P_m = (x + 2) P_(m-1) - P_(m-2)`. -/
def P : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => 3 + X
  | m + 2 => (X + 2) * P (m + 1) - P m

private theorem P_coeff (m : ℕ) : ∀ k, (P m).coeff k =
    (Nat.choose (m + k) (2 * k) : ℤ) + 2 * (Nat.choose (m + k) (2 * k + 1) : ℤ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k
    rcases m with _ | _ | m
    · rcases k with _ | k
      · simp [P]
      · simp [P, coeff_one, Nat.choose_eq_zero_of_lt (show k + 1 < 2 * (k + 1) by omega),
          Nat.choose_eq_zero_of_lt (show k + 1 < 2 * (k + 1) + 1 by omega)]
    · rcases k with _ | _ | k
      · simp [P]
      · simp [P, coeff_X]
      · simp [P, coeff_X, Nat.choose_eq_zero_of_lt (show 0 + 1 + (k + 2) < 2 * (k + 2) by omega),
          Nat.choose_eq_zero_of_lt (show 0 + 1 + (k + 2) < 2 * (k + 2) + 1 by omega)]
    · have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      show ((X + 2) * P (m + 1) - P m).coeff k = _
      rw [coeff_sub, add_mul, coeff_add, show (2 : Polynomial ℤ) = C 2 from rfl, coeff_C_mul]
      rcases k with _ | j
      · rw [coeff_X_mul_zero, h1, h0]
        simp
        ring
      · rw [coeff_X_mul, h1, h1, h0]
        simp only [show m + 1 + j = m + j + 1 by ring, show m + 1 + (j + 1) = m + j + 2 by ring,
          show m + (j + 1) = m + j + 1 by ring, show m + 1 + 1 + (j + 1) = m + j + 3 by ring,
          show 2 * (j + 1) = 2 * j + 2 by ring,
          Nat.choose_succ_succ', Nat.cast_add]
        ring

private theorem shear (m k : ℕ) : (P m).coeff k = ((pair (m + k)).2).coeff k := by
  have hw := werner_a208509 (m + k + 1) (by omega) k
  rw [show m + k + 1 - 1 = m + k by omega] at hw
  rw [P_coeff, hw, show 2 * k + 1 = (2 * k) + 1 from rfl, Nat.choose_succ_succ' (m + k) (2 * k)]
  push_cast
  ring

/-- Corollary 2 of the Ma–Zhang note on A208509 (André-Jeannin's `r = 2` coefficient theorem):
for every `m` and `k`, `[x^k] P_m = b_{m+k+1,k} = C(m+k, 2k) + 2 C(m+k, 2k+1)`, where
`b_{n,k} = [x^k] v_n` is the coefficient of the actual affine pair at stage `n - 1`. -/
theorem result : ∀ m k : ℕ, (P m).coeff k = ((pair (m + k)).2).coeff k ∧
    (P m).coeff k = (Nat.choose (m + k) (2 * k) : ℤ) + 2 * (Nat.choose (m + k) (2 * k + 1) : ℤ) :=
  fun m k => ⟨shear m k, P_coeff m k⟩

end
end D5.S1.Recurrence.Invariants.AffinePolynomialPairMorganVoyceShear
