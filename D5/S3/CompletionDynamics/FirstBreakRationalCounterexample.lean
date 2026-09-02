/- GID: D5/S3/CompletionDynamics/FirstBreakRationalCounterexample
   generality: G
   mirror-B: D5/B/S3/CompletionDynamics/FirstBreakRationalCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A first nonzero observation admits both rational and irrational first coordinates. -/

import Mathlib.NumberTheory.Real.Irrational

/-!
A trajectory has a first break here when its zeroth coordinate vanishes and
its first coordinate does not. Explicit rational and irrational trajectories
show that this condition alone does not determine arithmetic type.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.CompletionDynamics.FirstBreakRationalCounterexample

/-- The first observed coordinate is the first nonzero coordinate. -/
def HasFirstBreak (trajectory : ℕ → ℝ) : Prop :=
  trajectory 0 = 0 ∧ trajectory 1 ≠ 0

/-- A first break has both a rational witness and an irrational control
witness, so it cannot by itself force irrationality. -/
theorem first_break_does_not_force_irrationality :
    ∃ rationalTrajectory irrationalTrajectory : ℕ → ℝ,
      HasFirstBreak rationalTrajectory ∧
      ¬ Irrational (rationalTrajectory 1) ∧
      HasFirstBreak irrationalTrajectory ∧
      Irrational (irrationalTrajectory 1) := by
  refine ⟨fun n => if n = 0 then 0 else 1,
    fun n => if n = 0 then 0 else Real.sqrt 2, ?_⟩
  constructor
  · simp [HasFirstBreak]
  constructor
  · simpa using (Rat.not_irrational (1 : ℚ))
  constructor
  · simpa [HasFirstBreak] using irrational_sqrt_two.ne_zero
  · simpa using irrational_sqrt_two

#print axioms first_break_does_not_force_irrationality

end D5.S3.CompletionDynamics.FirstBreakRationalCounterexample
