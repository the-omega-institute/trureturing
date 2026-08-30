/- GID: D5/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius
   generality: G
   mirror-B: D5/B/S3/Weil/GoldenCriticalSpectrum/GoldenCriticalRadius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden exponential radial coordinates send the critical line to the unit radius and completed reflection to reciprocal radius. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle
import Mathlib.Data.Complex.Exponential

/-!
This is an exact change of radial coordinate on the complex plane. Applying it
to a zero set rewrites a Riemann-type critical-line statement as unit-radius
neutrality. No zero-location theorem is proved by the coordinate change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.GoldenCriticalSpectrum.GoldenCriticalRadius

open D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle

/-- Reflection across the critical line. -/
def criticalReflection (s : ℂ) : ℂ :=
  1 - Complex.conj s

/-- Signed normal displacement from the critical line. -/
def criticalOffset (s : ℂ) : ℝ :=
  s.re - 1 / 2

/-- Positive radial coordinate attached to the golden shell period. -/
def goldenCriticalRadius (s : ℂ) : ℝ :=
  Real.exp (goldenScalePeriod * criticalOffset s)

/-- The golden critical radius is always positive. -/
theorem golden_critical_radius_pos (s : ℂ) :
    0 < goldenCriticalRadius s := by
  unfold goldenCriticalRadius
  exact Real.exp_pos _

/-- Reflection negates the normal displacement. -/
theorem critical_offset_reflection (s : ℂ) :
    criticalOffset (criticalReflection s) = -criticalOffset s := by
  unfold criticalOffset criticalReflection
  simp
  ring

/-- The critical line is exactly the unit-radius locus. -/
theorem golden_critical_radius_eq_one_iff (s : ℂ) :
    goldenCriticalRadius s = 1 ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hExp :
        Real.exp (goldenScalePeriod * criticalOffset s) = Real.exp 0 := by
      simpa [goldenCriticalRadius] using h
    have hArg := Real.exp_injective hExp
    have hOffset : criticalOffset s = 0 := by
      apply (mul_eq_zero.mp hArg).resolve_left golden_scale_period_ne_zero
    unfold criticalOffset at hOffset
    linarith
  · intro h
    unfold goldenCriticalRadius criticalOffset
    rw [h]
    norm_num

/-- Completed reflection sends the radius to its reciprocal. -/
theorem golden_critical_radius_reflection (s : ℂ) :
    goldenCriticalRadius (criticalReflection s) =
      (goldenCriticalRadius s)⁻¹ := by
  rw [goldenCriticalRadius, critical_offset_reflection]
  simp [goldenCriticalRadius, Real.exp_neg]

/-- Every reflected pair has unit total radial charge. -/
theorem reflected_radius_product_one (s : ℂ) :
    goldenCriticalRadius s *
      goldenCriticalRadius (criticalReflection s) = 1 := by
  rw [golden_critical_radius_reflection]
  exact mul_inv_cancel₀ (ne_of_gt (golden_critical_radius_pos s))

/-- A set lies on the critical line exactly when all of its golden radii are
pointwise neutral. -/
theorem all_critical_iff_all_unit_radius (Z : Set ℂ) :
    (∀ s ∈ Z, s.re = 1 / 2) ↔
      (∀ s ∈ Z, goldenCriticalRadius s = 1) := by
  constructor <;> intro h s hs
  · exact (golden_critical_radius_eq_one_iff s).2 (h s hs)
  · exact (golden_critical_radius_eq_one_iff s).1 (h s hs)

#print axioms critical_offset_reflection
#print axioms golden_critical_radius_eq_one_iff
#print axioms golden_critical_radius_reflection
#print axioms reflected_radius_product_one
#print axioms all_critical_iff_all_unit_radius

end D5.S3.Weil.GoldenCriticalSpectrum.GoldenCriticalRadius
