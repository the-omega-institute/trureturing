/- GID: D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden completion curves share the same completed value while their first blow-up coordinate and tangent retain the observer origin. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
For an origin coefficient `c`, the source curve is the inverse cross-ratio
chart evaluated at `h*c`.  The parameter value `h = 0` is the completed point.
Its first derivative retains `c` and the fixed-point gap `sqrt 5`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.GoldenMobius.GoldenThreadBlowup

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization

/-- Inverse golden cross-ratio chart along the ray with origin coefficient
`c`. -/
def goldenThreadCurve (c h : ℝ) : ℝ :=
  (Real.goldenRatio - h * c * Real.goldenConj) / (1 - h * c)

@[simp]
theorem golden_thread_curve_zero (c : ℝ) :
    goldenThreadCurve c 0 = Real.goldenRatio := by
  simp [goldenThreadCurve]

/-- Difference from the completed fixed point in the inverse projective chart. -/
theorem golden_thread_curve_sub_golden {c h : ℝ}
    (hDen : 1 - h * c ≠ 0) :
    goldenThreadCurve c h - Real.goldenRatio =
      (h * c) * (Real.goldenRatio - Real.goldenConj) / (1 - h * c) := by
  unfold goldenThreadCurve
  field_simp [hDen]
  ring

/-- Difference from the conjugate fixed point in the inverse projective chart. -/
theorem golden_thread_curve_sub_conjugate {c h : ℝ}
    (hDen : 1 - h * c ≠ 0) :
    goldenThreadCurve c h - Real.goldenConj =
      (Real.goldenRatio - Real.goldenConj) / (1 - h * c) := by
  unfold goldenThreadCurve
  field_simp [hDen]
  ring

/-- The inverse chart recovers the prescribed projective coordinate exactly. -/
theorem golden_cross_ratio_thread_curve {c h : ℝ}
    (hDen : 1 - h * c ≠ 0) :
    goldenCrossRatio (goldenThreadCurve c h) = h * c := by
  rw [goldenCrossRatio, golden_thread_curve_sub_golden hDen,
    golden_thread_curve_sub_conjugate hDen]
  have hGap : Real.goldenRatio - Real.goldenConj ≠ 0 := by
    exact sub_ne_zero.mpr golden_fixed_points_ne
  field_simp [hDen, hGap]
  ring

/-- The inverse golden chart has first derivative `c(φ-ψ)` at completion. -/
theorem golden_thread_curve_hasDerivAt (c : ℝ) :
    HasDerivAt (goldenThreadCurve c)
      (c * (Real.goldenRatio - Real.goldenConj)) 0 := by
  have hHCraw : HasDerivAt (fun h : ℝ => c * h) c 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (x := 0)).const_mul c
  have hHC : HasDerivAt (fun h : ℝ => h * c) c 0 := by
    convert hHCraw using 1 <;> ring
  have hHCPsiRaw :
      HasDerivAt (fun h : ℝ => Real.goldenConj * (h * c))
        (Real.goldenConj * c) 0 := by
    simpa using hHC.const_mul Real.goldenConj
  have hHCPsi :
      HasDerivAt (fun h : ℝ => h * c * Real.goldenConj)
        (c * Real.goldenConj) 0 := by
    convert hHCPsiRaw using 1 <;> ring
  have hNumerator :
      HasDerivAt
        (fun h : ℝ => Real.goldenRatio - h * c * Real.goldenConj)
        (-(c * Real.goldenConj)) 0 := by
    simpa using
      (hasDerivAt_const (x := 0) Real.goldenRatio).sub hHCPsi
  have hDenominator :
      HasDerivAt (fun h : ℝ => 1 - h * c) (-c) 0 := by
    simpa using (hasDerivAt_const (x := 0) (1 : ℝ)).sub hHC
  have hQuotient := hNumerator.div hDenominator (by norm_num)
  convert hQuotient using 1
  · funext h
    simp only [goldenThreadCurve]
  · simp
    ring

/-- The tangent coefficient displays the discriminant gap `sqrt 5`. -/
theorem golden_thread_curve_hasDerivAt_sqrt_five (c : ℝ) :
    HasDerivAt (goldenThreadCurve c) (c * Real.sqrt 5) 0 := by
  simpa [Real.goldenRatio_sub_goldenConj] using
    golden_thread_curve_hasDerivAt c

/-- Two origin coefficients give the same completed value. -/
theorem golden_thread_completion_value_eq (c₁ c₂ : ℝ) :
    goldenThreadCurve c₁ 0 = goldenThreadCurve c₂ 0 := by
  simp

/-- Distinct origin coefficients give distinct completion tangents. -/
theorem golden_thread_tangent_injective :
    Function.Injective (fun c : ℝ => c * Real.sqrt 5) := by
  intro c₁ c₂ h
  have hSqrt : Real.sqrt 5 ≠ 0 := by positivity
  exact (mul_right_cancel₀ hSqrt h)

/-- A finite-depth geometric golden thread obtained by inserting the exact
projective multiplier into the inverse chart. -/
def goldenGeometricThread (c : ℝ) (n : ℕ) : ℝ :=
  goldenThreadCurve c (goldenProjectiveMultiplier ^ n)

/-- At any depth where the inverse affine chart is defined, the blow-up
coordinate is exactly `c * multiplier^n`. -/
theorem golden_geometric_thread_cross_ratio {c : ℝ} {n : ℕ}
    (hDen : 1 - goldenProjectiveMultiplier ^ n * c ≠ 0) :
    goldenCrossRatio (goldenGeometricThread c n) =
      goldenProjectiveMultiplier ^ n * c := by
  exact golden_cross_ratio_thread_curve hDen

/-- Since the multiplier is nonzero, renormalization recovers the origin
coefficient at every finite depth. -/
theorem golden_geometric_thread_origin_recovery {c : ℝ} {n : ℕ}
    (hDen : 1 - goldenProjectiveMultiplier ^ n * c ≠ 0) :
    (goldenProjectiveMultiplier⁻¹) ^ n *
        goldenCrossRatio (goldenGeometricThread c n) = c := by
  rw [golden_geometric_thread_cross_ratio hDen, ← mul_assoc, ← mul_pow]
  have hMultiplier : goldenProjectiveMultiplier ≠ 0 := by
    unfold goldenProjectiveMultiplier
    positivity
  rw [inv_mul_cancel₀ hMultiplier, one_pow, one_mul]

#print axioms golden_thread_curve_sub_golden
#print axioms golden_thread_curve_sub_conjugate
#print axioms golden_cross_ratio_thread_curve
#print axioms golden_thread_curve_hasDerivAt_sqrt_five
#print axioms golden_thread_tangent_injective
#print axioms golden_geometric_thread_origin_recovery

end D5.S3.CompletionDynamics.GoldenMobius.GoldenThreadBlowup
