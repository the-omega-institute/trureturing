/- GID: D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The reciprocal golden Mobius map has the golden ratio and its conjugate as fixed points and preserves the positive half-line. -/

import Mathlib.NumberTheory.Real.GoldenRatio

/-!
The source theory uses `T(x) = 1 + 1/x`.  Lean division is total, so geometric
statements about the Mobius map carry explicit nonzero hypotheses in downstream
modules.  The fixed-point identities themselves are valid at the two nonzero
golden roots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap

open scoped goldenRatio

/-- The real affine chart of the golden Mobius transformation. -/
def goldenMobius (x : ℝ) : ℝ :=
  1 + 1 / x

/-- The exact projective contraction multiplier appearing after cross-ratio
linearization. -/
def goldenProjectiveMultiplier : ℝ :=
  -(Real.goldenRatio⁻¹) ^ 2

/-- The positive golden root is a fixed point. -/
theorem golden_mobius_fixed_golden :
    goldenMobius Real.goldenRatio = Real.goldenRatio := by
  rw [goldenMobius, one_div, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

/-- The negative conjugate golden root is the second fixed point. -/
theorem golden_mobius_fixed_conjugate :
    goldenMobius Real.goldenConj = Real.goldenConj := by
  rw [goldenMobius, one_div, Real.inv_goldenConj]
  linarith [Real.goldenRatio_add_goldenConj]

/-- The two fixed points are distinct. -/
theorem golden_fixed_points_ne :
    Real.goldenRatio ≠ Real.goldenConj := by
  apply sub_ne_zero.mp
  rw [Real.goldenRatio_sub_goldenConj]
  positivity

/-- Their oriented gap is the square root of the discriminant. -/
theorem golden_fixed_point_gap :
    Real.goldenRatio - Real.goldenConj = Real.sqrt 5 :=
  Real.goldenRatio_sub_goldenConj

/-- Positive starting points remain in the positive affine chart. -/
theorem golden_mobius_pos {x : ℝ} (hx : 0 < x) :
    0 < goldenMobius x := by
  unfold goldenMobius
  have hInv : 0 < 1 / x := one_div_pos.mpr hx
  linarith

/-- The projective multiplier can equivalently be read from the stable golden
conjugate eigenvalue. -/
theorem golden_projective_multiplier_eq_neg_conjugate_sq :
    goldenProjectiveMultiplier = -(Real.goldenConj ^ 2) := by
  rw [goldenProjectiveMultiplier, Real.inv_goldenRatio]
  ring

/-- Probe excluding a totalized-division artefact from the geometric fixed
points: zero is not fixed by the affine formula. -/
example : goldenMobius 0 ≠ 0 := by
  norm_num [goldenMobius]

#print axioms golden_mobius_fixed_golden
#print axioms golden_mobius_fixed_conjugate
#print axioms golden_fixed_points_ne
#print axioms golden_mobius_pos
#print axioms golden_projective_multiplier_eq_neg_conjugate_sq

end D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
