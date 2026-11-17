/- GID: D5/S3/Analytic/Chebyshev/PositivityThreshold
   generality: G
   mirror-B: D5/B/S3/Analytic/Chebyshev/PositivityThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every Chebyshev value T_n(s) with n ≥ 1 is positive exactly when s ≥ 1. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Positivity of all Chebyshev values at a point

For a real number `s`, the values `T_n(s)` of the Chebyshev polynomials of the first kind
are positive for every `n ≥ 1` exactly when `s ≥ 1`.

For `s ≥ 1` every value is at least `1`. For `s ≤ -1` already `T_1(s) = s` is negative.
For `-1 < s < 1` write `s = cos α` with `0 < α < π`; then `T_n(s) = cos (n α)`, and the
index `n₀ = ⌊π / (2α)⌋₊ + 1` is the first index with `cos (n₀ α) < 0`: the angles
`n α` with `n < n₀` lie in `[0, π/2]`, and `n₀ α` lies in `(π/2, π/2 + α)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Polynomial Real

namespace D5.S3.Analytic.Chebyshev.PositivityThreshold

/-- For `0 < α < π` and `n₀ = ⌊π / (2α)⌋₊ + 1`, the cosine `cos (n₀ α)` is negative,
while `cos (n α)` is nonnegative for every natural `n < n₀`. -/
theorem cos_floor_succ_mul_neg_and_cos_nonneg_before {α : ℝ} (hα : 0 < α)
    (hαπ : α < π) :
    Real.cos (((⌊π / (2 * α)⌋₊ + 1 : ℕ) : ℝ) * α) < 0 ∧
      ∀ n : ℕ, n < ⌊π / (2 * α)⌋₊ + 1 → 0 ≤ Real.cos ((n : ℝ) * α) := by
  have hx : 0 ≤ π / (2 * α) := by positivity
  have hfloor : (⌊π / (2 * α)⌋₊ : ℝ) ≤ π / (2 * α) := Nat.floor_le hx
  have hsucc : π / (2 * α) < (⌊π / (2 * α)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmul : π / (2 * α) * α = π / 2 := by
    field_simp
  constructor
  · push_cast
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · calc π / 2 = π / (2 * α) * α := hmul.symm
        _ < ((⌊π / (2 * α)⌋₊ : ℝ) + 1) * α := mul_lt_mul_of_pos_right hsucc hα
    · calc ((⌊π / (2 * α)⌋₊ : ℝ) + 1) * α ≤ (π / (2 * α) + 1) * α :=
            mul_le_mul_of_nonneg_right (by linarith) hα.le
        _ = π / 2 + α := by rw [add_mul, hmul, one_mul]
        _ < π + π / 2 := by linarith
  · intro n hn
    have hn' : (n : ℝ) ≤ π / (2 * α) :=
      le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hn) hfloor
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have : 0 ≤ (n : ℝ) * α := by positivity
      linarith [Real.pi_pos]
    · calc (n : ℝ) * α ≤ π / (2 * α) * α := mul_le_mul_of_nonneg_right hn' hα.le
        _ = π / 2 := hmul

/-- The values `T_n(s)` of the Chebyshev polynomials of the first kind at a real point `s`
are positive for every `n ≥ 1` if and only if `1 ≤ s`. -/
theorem forall_pos_eval_T_iff_one_le (s : ℝ) :
    (∀ n : ℕ, 1 ≤ n → 0 < (Chebyshev.T ℝ (n : ℤ)).eval s) ↔ 1 ≤ s := by
  constructor
  · intro h
    by_contra hs
    push_neg at hs
    rcases le_or_gt s (-1) with hneg | hneg
    · have h1 := h 1 le_rfl
      simp only [Nat.cast_one, Chebyshev.T_one, eval_X] at h1
      linarith
    · set α := Real.arccos s with hαdef
      have hα : 0 < α := Real.arccos_pos.mpr hs
      have hαπ : α < π := Real.arccos_lt_pi.mpr hneg
      have hcos : Real.cos α = s := Real.cos_arccos hneg.le hs.le
      have hneg_value := (cos_floor_succ_mul_neg_and_cos_nonneg_before hα hαπ).1
      have hpos := h (⌊π / (2 * α)⌋₊ + 1) (Nat.le_add_left 1 _)
      rw [← hcos, Chebyshev.T_real_cos] at hpos
      push_cast at hpos hneg_value
      linarith
  · intro hs n _
    exact lt_of_lt_of_le zero_lt_one (Chebyshev.one_le_eval_T_real (n : ℤ) hs)

end D5.S3.Analytic.Chebyshev.PositivityThreshold
