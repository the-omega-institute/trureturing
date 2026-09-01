/- GID: D5/S3/ObserverMemory/FourierFibers/SymmetryBreakingObservabilityGain
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/SymmetryBreakingObservabilityGain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Splitting an exact two-mode degeneracy turns a persistent hidden
     fiber into a faithful two-sample time readout. -/

import D5.S3.ObserverMemory.FourierFibers.DegenerateModeHiddenFiber
import D5.S3.ObserverMemory.FourierFibers.TemporalReflectionBreakVisibility

/-!
This module records an information-theoretic effect of symmetry breaking.  An
exact spectral degeneracy hides an antisymmetric amplitude at every time.  Once
the two modal multipliers separate, the first two scalar time samples form an
invertible Vandermonde readout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.SymmetryBreakingObservabilityGain

open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
open D5.S3.ObserverMemory.FourierFibers.DegenerateModeHiddenFiber

/-- A two-mode spectrum after a degeneracy has split. -/
def splitModes (left right : ℂ) : Fin 2 → ℂ
  | ⟨0, _⟩ => left
  | ⟨1, _⟩ => right

/-- Distinct split eigenvalues give an injective node family. -/
theorem split_modes_injective {left right : ℂ} (hSplit : left ≠ right) :
    Function.Injective (splitModes left right) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [splitModes]

/-- The first two time samples recover both amplitudes after the split. -/
theorem split_first_time_window_injective
    {left right : ℂ} (hSplit : left ≠ right) :
    Function.Injective
      (firstCrystalTimeWindow (splitModes left right)) :=
  first_crystal_time_window_injective (split_modes_injective hSplit)

/-- Exact degeneracy has a persistent hidden direction, whereas any genuine
split gives a faithful two-sample observer. -/
theorem symmetry_breaking_observability_gain
    {left right : ℂ} (hSplit : left ≠ right) :
    (¬ Function.Injective
        (fun amplitudes : Fin 2 → ℂ =>
          fun time : ℕ =>
            crystalTimeSample (degenerateModes left) amplitudes time)) ∧
      Function.Injective
        (firstCrystalTimeWindow (splitModes left right)) := by
  exact ⟨all_time_trace_not_injective left,
    split_first_time_window_injective hSplit⟩

/-- A concrete nonvacuous split. -/
example :
    Function.Injective
      (firstCrystalTimeWindow (splitModes 0 1)) :=
  split_first_time_window_injective (by norm_num)

#print axioms split_modes_injective
#print axioms split_first_time_window_injective
#print axioms symmetry_breaking_observability_gain

end D5.S3.ObserverMemory.FourierFibers.SymmetryBreakingObservabilityGain
