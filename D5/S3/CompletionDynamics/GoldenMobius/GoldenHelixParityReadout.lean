/- GID: D5/S3/CompletionDynamics/GoldenMobius/GoldenHelixParityReadout
   generality: I
   mirror-B: none(waiver:new-golden-observer-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden helix orientation flips at odd depth and returns at even depth while the hidden level advances. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
import D5.S3.ObserverMemory.Refinement.InvolutiveReadoutCompletion
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.GoldenMobius.GoldenHelixParityReadout

open D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
open D5.S3.ObserverMemory.Refinement.InvolutiveReadoutCompletion

/-- The golden helix viewed only through its orientation coordinate. -/
def goldenOrientationSystem :
    InvolutiveReadoutSystem GoldenHelixState Bool where
  step := goldenHelixStep
  readout := GoldenHelixState.orientation
  flip := Bool.not
  flip_involutive := by
    intro orientation
    cases orientation <;> rfl
  readout_step := goldenHelixStep_orientation

private theorem bool_not_ne_self (value : Bool) : Bool.not value ≠ value := by
  cases value <;> decide

/-- Every even number of golden helix steps restores the orientation readout. -/
theorem golden_helix_even_orientation_completion
    (state : GoldenHelixState) {steps : ℕ} (heven : Even steps) :
    ((goldenHelixStep^[steps]) state).orientation = state.orientation := by
  simpa [goldenOrientationSystem] using
    even_iterate_completes_readout goldenOrientationSystem state heven

/-- Every odd number of golden helix steps lies on the opposite orientation
sheet. -/
theorem golden_helix_odd_orientation_flip
    (state : GoldenHelixState) {steps : ℕ} (hodd : Odd steps) :
    ((goldenHelixStep^[steps]) state).orientation =
      Bool.not state.orientation := by
  simpa [goldenOrientationSystem] using
    odd_iterate_flips_readout goldenOrientationSystem state hodd

/-- Odd golden depth is visibly broken in the orientation channel. -/
theorem golden_helix_odd_orientation_breaking
    (state : GoldenHelixState) {steps : ℕ} (hodd : Odd steps) :
    ((goldenHelixStep^[steps]) state).orientation ≠ state.orientation := by
  rw [golden_helix_odd_orientation_flip state hodd]
  exact bool_not_ne_self state.orientation

/-- Two steps complete the orientation pair while the full helix state remains
at a different level. This is the exact boundary of the phrase "even
completion" in the current golden model. -/
theorem golden_helix_two_step_orientation_complete_state_distinct
    (state : GoldenHelixState) :
    (goldenHelixStep (goldenHelixStep state)).orientation =
        state.orientation ∧
      goldenHelixStep (goldenHelixStep state) ≠ state := by
  constructor
  · exact goldenHelixStep_twice_orientation state
  · intro hstate
    have hlevel := congrArg GoldenHelixState.level hstate
    simp only [goldenHelixStep_level] at hlevel
    omega

#print axioms golden_helix_even_orientation_completion
#print axioms golden_helix_odd_orientation_flip
#print axioms golden_helix_odd_orientation_breaking
#print axioms golden_helix_two_step_orientation_complete_state_distinct

end D5.S3.CompletionDynamics.GoldenMobius.GoldenHelixParityReadout
