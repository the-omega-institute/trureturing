/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairDegrees
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairDegrees
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Degree.Defs]
   utility: none
   digest: The affine pair's companion u-coefficients and the degrees of u_n and v_n. -/

import D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
import Mathlib.Algebra.Polynomial.Degree.Defs

/-! The companion coefficient formula and the degrees of the affine polynomial pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairDegrees

open Polynomial D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
noncomputable section

private theorem natDegree_v (n : ℕ) : ((pair (n - 1)).2).natDegree = (n - 1) / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [(pair_coeff (n - 1) k).2]
    have hk' : (n - 1) / 2 < k := by exact_mod_cast hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · rw [(pair_coeff (n - 1) ((n - 1) / 2)).2]
    have : 0 < Nat.choose (n - 1 + 1) (2 * ((n - 1) / 2) + 1) := Nat.choose_pos (by omega)
    positivity

private theorem natDegree_u (n : ℕ) (hn : 1 ≤ n) : ((pair (n - 1)).1).natDegree = n / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [(pair_coeff (n - 1) k).1]
    have hk' : n / 2 < k := by exact_mod_cast hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp only [show k ≠ 0 by omega, ↓reduceIte]
    simp
  · rw [(pair_coeff (n - 1) (n / 2)).1]
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      norm_num
    · have : 0 < Nat.choose (n - 1 + 1) (2 * (n / 2)) := Nat.choose_pos (by omega)
      simp only [show n / 2 ≠ 0 by omega, ↓reduceIte, sub_zero]
      positivity

private theorem v_ne_zero (n : ℕ) : (pair (n - 1)).2 ≠ 0 := by
  intro h
  have h0 := (pair_coeff (n - 1) 0).2
  rw [h] at h0
  have : 0 < Nat.choose (n - 1 + 1) 1 := Nat.choose_pos (by omega)
  simp at h0
  omega

private theorem u_ne_zero (n : ℕ) : (pair (n - 1)).1 ≠ 0 := by
  intro h
  have h0 := (pair_coeff (n - 1) 0).1
  rw [h] at h0
  simp at h0

/-- Theorem 1 of the Ma–Zhang note on A208509: for `n ≥ 1`, `u_n = (pair (n - 1)).1` has
`[x^k] u_n = C(n-1, 2k) + C(n, 2k) - [k = 0]` for every `k`, and the degrees are
`deg v_n = ⌊(n - 1)/2⌋` and `deg u_n = ⌊n/2⌋` (both polynomials are nonzero). -/
theorem result :
    (∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, ((pair (n - 1)).1).coeff k =
      (Nat.choose (n - 1) (2 * k) : ℤ) + (Nat.choose n (2 * k) : ℤ) -
        (if k = 0 then 1 else 0)) ∧
    (∀ n : ℕ, 1 ≤ n → ((pair (n - 1)).2).degree = ((n - 1) / 2 : ℕ)) ∧
    (∀ n : ℕ, 1 ≤ n → ((pair (n - 1)).1).degree = (n / 2 : ℕ)) := by
  refine ⟨fun n hn k => ?_, fun n _ => ?_, fun n hn => ?_⟩
  · have h := (pair_coeff (n - 1) k).1
    rwa [show n - 1 + 1 = n by omega] at h
  · rw [degree_eq_natDegree (v_ne_zero n), natDegree_v n]
  · rw [degree_eq_natDegree (u_ne_zero n), natDegree_u n hn]

end
end D5.S1.Recurrence.Invariants.AffinePolynomialPairDegrees
