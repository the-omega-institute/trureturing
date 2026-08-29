/- GID: D5/S3/Analytic/Characterizations/GoldenTransferTriangle
   generality: I
   mirror-B: D5/B/S3/Analytic/Characterizations/GoldenTransferTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden disk radius controls the fixed point, derivative, and orbit scale. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace D5.S3.Analytic.Characterizations.GoldenTransferTriangle

open Set
open scoped goldenRatio

/-!
Search receipt (2026-08-28): pinned Mathlib supplies `Real.goldenRatio_sq`,
`Real.inv_goldenRatio`, `HasDerivAt.div`, and the real exponential-log identities.
No D5 theorem states the combined sharp-radius, fixed-point, derivative, and orbit-scale result.
-/

/-- The strict disk test has sharp radius `φ`; at its reciprocal fixed point, the inverse branch
has derivative magnitude `φ⁻²`, while the length `4 log φ` exponentiates to `φ⁻⁴`. -/
theorem golden_transfer_triangle :
    IsLUB {r : ℝ | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r}
      Real.goldenRatio ∧
    Real.goldenRatio - 1 = Real.goldenRatio⁻¹ ∧
    |deriv (fun x : ℝ => 1 / (x + 1)) (Real.goldenRatio - 1)| =
      (Real.goldenRatio⁻¹) ^ 2 ∧
    Real.exp (-(4 * Real.log Real.goldenRatio)) = (Real.goldenRatio⁻¹) ^ 4 := by
  have hset :
      {r : ℝ | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r} =
        Set.Ico 1 Real.goldenRatio := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, htest⟩
      refine ⟨h1, ?_⟩
      have hden : 0 < 2 - r := by linarith
      rw [div_lt_iff₀ hden] at htest
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    · rintro ⟨h1, hr⟩
      have h2 : r < 2 := hr.trans Real.goldenRatio_lt_two
      refine ⟨h1, h2, ?_⟩
      have hden : 0 < 2 - r := by linarith
      rw [div_lt_iff₀ hden]
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hlub : IsLUB {r : ℝ | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r}
      Real.goldenRatio := by
    rw [hset]
    exact isLUB_Ico Real.one_lt_goldenRatio
  have hfixed : Real.goldenRatio - 1 = Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hderiv :
      deriv (fun x : ℝ => 1 / (x + 1)) (Real.goldenRatio - 1) =
        -(Real.goldenRatio⁻¹) ^ 2 := by
    have hne : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
    have hd := (hasDerivAt_const (𝕜 := ℝ) (Real.goldenRatio - 1) 1).div
      ((hasDerivAt_id (𝕜 := ℝ) (x := Real.goldenRatio - 1)).add_const 1)
      (by simpa using hne)
    have hpow : -(Real.goldenRatio⁻¹) ^ 2 =
        -1 / Real.goldenRatio ^ 2 := by
      rw [inv_pow, div_eq_mul_inv]
      ring
    convert hd.deriv using 1
    · congr 1
    · simpa only [id_eq, sub_add_cancel, zero_mul, one_mul, zero_sub] using hpow
  have habs :
      |deriv (fun x : ℝ => 1 / (x + 1)) (Real.goldenRatio - 1)| =
        (Real.goldenRatio⁻¹) ^ 2 := by
    rw [hderiv, abs_neg, abs_of_pos]
    positivity
  have hexp : Real.exp (-(4 * Real.log Real.goldenRatio)) =
      (Real.goldenRatio⁻¹) ^ 4 := by
    rw [show -(4 * Real.log Real.goldenRatio) =
      -Real.log Real.goldenRatio + -Real.log Real.goldenRatio +
        -Real.log Real.goldenRatio + -Real.log Real.goldenRatio by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_neg,
      Real.exp_log Real.goldenRatio_pos]
    ring
  exact ⟨hlub, hfixed, habs, hexp⟩

end D5.S3.Analytic.Characterizations.GoldenTransferTriangle
