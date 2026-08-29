/- GID: D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenAngleTraceBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The trace observer sends the thirty-six-degree rotation angle to the golden ratio while identifying opposite chiralities. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
The bridge from angle to golden ratio is the real trace observable
`theta ↦ 2 cos theta`.  At `theta = pi / 5` it returns the golden ratio.  The
same observable is even, so it deliberately forgets the sign of the rotation
angle.  This is a concrete observer quotient, rather than an identification of
angle and ratio as the same typed object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.GoldenAngleTraceBridge

open scoped goldenRatio

/-- The thirty-six-degree angle in radians. -/
def goldenAngle : ℝ :=
  Real.pi / 5

/-- Real trace of a planar rotation. -/
def rotationTrace (theta : ℝ) : ℝ :=
  2 * Real.cos theta

/-- The trace of the thirty-six-degree rotation is exactly the golden ratio. -/
theorem golden_angle_trace_eq_golden_ratio :
    rotationTrace goldenAngle = Real.goldenRatio := by
  rw [rotationTrace, goldenAngle, Real.cos_pi_div_five]
  ring

/-- The trace observer forgets orientation. -/
theorem rotation_trace_neg (theta : ℝ) :
    rotationTrace (-theta) = rotationTrace theta := by
  simp [rotationTrace]

/-- The golden angle is genuinely distinct from its reflected angle. -/
theorem golden_angle_ne_neg :
    goldenAngle ≠ -goldenAngle := by
  have hPositive : 0 < goldenAngle := by
    unfold goldenAngle
    positivity
  linarith

/-- Consequently the trace observer is not injective. -/
theorem rotation_trace_not_injective :
    ¬ Function.Injective rotationTrace := by
  intro hInjective
  apply golden_angle_ne_neg
  apply hInjective
  exact (rotation_trace_neg goldenAngle).symm

/-- The observed trace retains the golden quadratic relation. -/
theorem golden_angle_trace_quadratic :
    rotationTrace goldenAngle ^ 2 =
      rotationTrace goldenAngle + 1 := by
  rw [golden_angle_trace_eq_golden_ratio]
  exact Real.goldenRatio_sq

/-- The trace bridge transports the golden ratio into its reciprocal fixed-point
presentation. -/
theorem golden_angle_trace_reciprocal_fixed :
    1 + 1 / rotationTrace goldenAngle = rotationTrace goldenAngle := by
  rw [golden_angle_trace_eq_golden_ratio, one_div,
    Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

#print axioms golden_angle_trace_eq_golden_ratio
#print axioms rotation_trace_neg
#print axioms golden_angle_ne_neg
#print axioms rotation_trace_not_injective
#print axioms golden_angle_trace_quadratic
#print axioms golden_angle_trace_reciprocal_fixed

end D5.S3.Observer.GoldenCoding.GoldenAngleTraceBridge
