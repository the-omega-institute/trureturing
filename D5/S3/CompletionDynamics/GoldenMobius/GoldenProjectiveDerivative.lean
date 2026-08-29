/- GID: D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The derivative of the golden Mobius map at its attracting fixed point is exactly the projective multiplier minus the inverse golden ratio squared. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization

/-- Ordinary differentiation at the complete fixed point gives the same
multiplier as the exact projective conjugacy. -/
theorem golden_mobius_hasDerivAt :
    HasDerivAt goldenMobius goldenProjectiveMultiplier
      Real.goldenRatio := by
  have h :=
    (hasDerivAt_const (𝕜 := ℝ) Real.goldenRatio 1).add
      (hasDerivAt_inv Real.goldenRatio_ne_zero)
  simpa [goldenMobius, one_div, goldenProjectiveMultiplier, inv_pow] using h

/-- Evaluation of `deriv` at the golden fixed point. -/
theorem deriv_golden_mobius_at_golden :
    deriv goldenMobius Real.goldenRatio = goldenProjectiveMultiplier :=
  golden_mobius_hasDerivAt.deriv

/-- The projective multiplier has the expected positive magnitude. -/
theorem abs_golden_projective_multiplier :
    |goldenProjectiveMultiplier| = (Real.goldenRatio⁻¹) ^ 2 := by
  simp [goldenProjectiveMultiplier]

/-- The completion derivative is a strict contraction in the projective
coordinate. -/
theorem abs_golden_projective_multiplier_lt_one :
    |goldenProjectiveMultiplier| < 1 := by
  rw [abs_golden_projective_multiplier]
  let a : ℝ := Real.goldenRatio⁻¹
  have haPos : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr Real.goldenRatio_pos
  have haLt : a < 1 := by
    dsimp [a]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hProduct : 0 < (1 - a) * (1 + a) :=
    mul_pos (sub_pos.mpr haLt) (by linarith)
  dsimp [a] at *
  nlinarith

/-- In the linearized coordinate itself, multiplication by the golden
multiplier has derivative equal to that multiplier at the completed point. -/
theorem linearized_golden_hasDerivAt_zero :
    HasDerivAt (fun y : ℝ => goldenProjectiveMultiplier * y)
      goldenProjectiveMultiplier 0 := by
  simpa using (hasDerivAt_id (𝕜 := ℝ) (x := 0)).const_mul
    goldenProjectiveMultiplier

#print axioms golden_mobius_hasDerivAt
#print axioms deriv_golden_mobius_at_golden
#print axioms abs_golden_projective_multiplier_lt_one
#print axioms linearized_golden_hasDerivAt_zero

end D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative
