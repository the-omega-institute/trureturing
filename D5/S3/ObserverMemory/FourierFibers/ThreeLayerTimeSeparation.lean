/- GID: D5/S3/ObserverMemory/FourierFibers/ThreeLayerTimeSeparation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/ThreeLayerTimeSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Clock iteration, observer refinement depth, and first symmetry-break visibility are separated by existing finite witnesses. -/

import D5.S3.ObserverMemory.FourierFibers.SymmetryBreakingObservabilityGain
import D5.S3.ObserverMemory.PredictionCertificates.ClockTimeVersusRefinementDepth

/-!
The repository already owns the constituent notions and witnesses. This module
only composes them. Clock duration does not determine predictive refinement
depth. For a reflected two-mode pair, the static scalar readout collides, one
nondegenerate time step separates the selected branches, exact degeneracy has
an all-time hidden direction, and a genuine modal split makes the first full
window faithful.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.ThreeLayerTimeSeparation

open D5.S3.ObserverMemory.FourierFibers.DegenerateModeHiddenFiber
open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
open D5.S3.ObserverMemory.FourierFibers.SymmetryBreakingObservabilityGain
open D5.S3.ObserverMemory.FourierFibers.TemporalReflectionBreakVisibility
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionCertificates.ClockTimeVersusRefinementDepth

/-- The three time notions are simultaneously separated by concrete finite
witnesses already frozen in the repository. -/
theorem three_layer_time_separation {z : ℂ} (hBreak : z ≠ z⁻¹) :
    ((∃ (tau : Unit → Unit) (q : Unit → Unit),
        (∀ n : ℕ, (tau^[n]) () = ()) ∧ completionDepth tau q = 0) ∧
      (∃ (tau : DelayedState → DelayedState) (q : DelayedState → Bool),
        tau .zero = .one ∧ 2 ≤ completionDepth tau q)) ∧
    crystalTimeSample (reflectedModes z) firstBranch 0 =
      crystalTimeSample (reflectedModes z) secondBranch 0 ∧
    crystalTimeSample (reflectedModes z) firstBranch 1 ≠
      crystalTimeSample (reflectedModes z) secondBranch 1 ∧
    (¬ Function.Injective
        (fun amplitudes : Fin 2 → ℂ =>
          fun time : ℕ =>
            crystalTimeSample (degenerateModes z) amplitudes time)) ∧
    Function.Injective
      (firstCrystalTimeWindow (splitModes z z⁻¹)) := by
  refine ⟨clock_time_does_not_determine_refinement_depth,
    reflected_branches_static_collision z,
    reflected_branches_time_one_separation hBreak, ?_⟩
  exact symmetry_breaking_observability_gain hBreak

/-- The reflected split hypothesis is concretely satisfiable. -/
example : (2 : ℂ) ≠ (2 : ℂ)⁻¹ := by norm_num

#print axioms three_layer_time_separation

end D5.S3.ObserverMemory.FourierFibers.ThreeLayerTimeSeparation
