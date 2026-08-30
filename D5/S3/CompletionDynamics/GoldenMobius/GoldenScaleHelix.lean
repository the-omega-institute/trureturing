/- GID: D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden completion lifts to a helix whose deck step advances one scale period and reverses orientation. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The quotient of logarithmic scale by the period `2 log φ` is the golden scale
circle discussed in the theory document.  Instead of introducing a second
quotient API, this module formalizes its universal-cover dynamics.

One deck step raises the completion level, translates the logarithmic scale by
one positive period, and flips an orientation bit.  Two steps restore the
orientation while translating by two periods.  This is the precise elementary
content of the “golden completion helix” metaphor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative

/-- One full positive golden scale period in logarithmic coordinates. -/
def goldenScalePeriod : ℝ :=
  2 * Real.log Real.goldenRatio

/-- The golden logarithmic scale period is strictly positive. -/
theorem golden_scale_period_pos :
    0 < goldenScalePeriod := by
  unfold goldenScalePeriod
  exact mul_pos (by norm_num) (Real.log_pos Real.one_lt_goldenRatio)

/-- The logarithmic scale period is exactly the negative logarithm of the
absolute golden projective multiplier. -/
theorem golden_scale_period_eq_neg_log_multiplier :
    goldenScalePeriod =
      -Real.log |goldenProjectiveMultiplier| := by
  rw [abs_golden_projective_multiplier, Real.log_pow, Real.log_inv]
  unfold goldenScalePeriod
  ring

/-- A point on the universal cover of the golden scale circle, together with
its completion level and orientation sheet. -/
structure GoldenHelixState where
  level : ℕ
  scaleLift : ℝ
  orientation : Bool

/-- One golden completion step on the universal-cover helix. -/
def goldenHelixStep (state : GoldenHelixState) : GoldenHelixState where
  level := state.level + 1
  scaleLift := state.scaleLift + goldenScalePeriod
  orientation := !state.orientation

@[simp] theorem goldenHelixStep_level (state : GoldenHelixState) :
    (goldenHelixStep state).level = state.level + 1 :=
  rfl

@[simp] theorem goldenHelixStep_scaleLift (state : GoldenHelixState) :
    (goldenHelixStep state).scaleLift =
      state.scaleLift + goldenScalePeriod :=
  rfl

@[simp] theorem goldenHelixStep_orientation (state : GoldenHelixState) :
    (goldenHelixStep state).orientation = !state.orientation :=
  rfl

/-- Two completion turns restore the orientation sheet. -/
@[simp] theorem goldenHelixStep_twice_orientation
    (state : GoldenHelixState) :
    (goldenHelixStep (goldenHelixStep state)).orientation =
      state.orientation := by
  simp [goldenHelixStep]

/-- Two completion turns add exactly two golden scale periods. -/
theorem goldenHelixStep_twice_scaleLift
    (state : GoldenHelixState) :
    (goldenHelixStep (goldenHelixStep state)).scaleLift =
      state.scaleLift + 2 * goldenScalePeriod := by
  simp [goldenHelixStep]
  ring

/-- Every completion turn strictly increases the lifted scale coordinate. -/
theorem goldenHelixStep_scaleLift_strict
    (state : GoldenHelixState) :
    state.scaleLift < (goldenHelixStep state).scaleLift := by
  rw [goldenHelixStep_scaleLift]
  linarith [golden_scale_period_pos]

#print axioms golden_scale_period_pos
#print axioms golden_scale_period_eq_neg_log_multiplier
#print axioms goldenHelixStep_level
#print axioms goldenHelixStep_scaleLift
#print axioms goldenHelixStep_orientation
#print axioms goldenHelixStep_twice_orientation
#print axioms goldenHelixStep_twice_scaleLift
#print axioms goldenHelixStep_scaleLift_strict

end D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
