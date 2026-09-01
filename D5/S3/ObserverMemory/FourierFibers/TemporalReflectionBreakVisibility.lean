/- GID: D5/S3/ObserverMemory/FourierFibers/TemporalReflectionBreakVisibility
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/TemporalReflectionBreakVisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A static scalar readout identifies reflected modal branches, while one nondegenerate time step separates them. -/

import D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.TemporalReflectionBreakVisibility

open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

/-- A reflected pair of modal multipliers. -/
def reflectedModes (z : ℂ) : Fin 2 → ℂ
  | ⟨0, _⟩ => z
  | ⟨1, _⟩ => z⁻¹

/-- Unit amplitude concentrated in the first reflected branch. -/
def firstBranch : Fin 2 → ℂ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

/-- Unit amplitude concentrated in the second reflected branch. -/
def secondBranch : Fin 2 → ℂ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

/-- At time zero, a scalar readout cannot distinguish which reflected branch
carries the unit amplitude. -/
theorem reflected_branches_static_collision (z : ℂ) :
    crystalTimeSample (reflectedModes z) firstBranch 0 =
      crystalTimeSample (reflectedModes z) secondBranch 0 := by
  simp [crystalTimeSample, reflectedModes, firstBranch, secondBranch,
    Fin.sum_univ_two]

/-- At time one, a nondegenerate reflected pair becomes distinguishable. -/
theorem reflected_branches_time_one_separation {z : ℂ}
    (hBreak : z ≠ z⁻¹) :
    crystalTimeSample (reflectedModes z) firstBranch 1 ≠
      crystalTimeSample (reflectedModes z) secondBranch 1 := by
  simpa [crystalTimeSample, reflectedModes, firstBranch, secondBranch,
    Fin.sum_univ_two] using hBreak

/-- The two hidden branch states are genuinely different. -/
theorem firstBranch_ne_secondBranch : firstBranch ≠ secondBranch := by
  intro h
  have hAtZero := congrFun h (0 : Fin 2)
  norm_num [firstBranch, secondBranch] at hAtZero

/-- The time-zero observer is noninjective on the two branch states. -/
theorem static_reflection_readout_not_injective (z : ℂ) :
    ¬ Function.Injective
      (fun amplitudes : Fin 2 → ℂ =>
        crystalTimeSample (reflectedModes z) amplitudes 0) := by
  intro hInjective
  exact firstBranch_ne_secondBranch
    (hInjective (reflected_branches_static_collision z))

#print axioms reflected_branches_static_collision
#print axioms reflected_branches_time_one_separation
#print axioms firstBranch_ne_secondBranch
#print axioms static_reflection_readout_not_injective

end D5.S3.ObserverMemory.FourierFibers.TemporalReflectionBreakVisibility
