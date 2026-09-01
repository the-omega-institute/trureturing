/- GID: D5/S3/ObserverMemory/FourierFibers/SpectralObservationStabilityDepthBound
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/SpectralObservationStabilityDepthBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A separated finite diagonal spectrum stabilizes the canonical observer by the last required Vandermonde sample. -/

import D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge
import D5.S3.Observer.Separation.FiniteObservationRefinementBound

/-!
Library-first audit:
* `observationStabilityDepth` is reused from the canonical finite-observation
  refinement theory.
* The finite spectral readout is identified with `futureReadoutWord` by the
  existing spectral bridge, and injectivity comes from finite Vandermonde
  tomography.
* No competing temporal-depth definition is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.SpectralObservationStabilityDepthBound

open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
open D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.Observer.Separation.FiniteObservationRefinementBound

universe u

variable {K : Type u} [Field K]

/-- For `depth + 1` pairwise distinct modes, the canonical future word through
`depth` is already injective. -/
theorem spectral_future_word_injective
    {depth : ℕ} {modes : Fin (depth + 1) → K}
    (hModes : Function.Injective modes) :
    Function.Injective
      (futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout depth) := by
  intro left right hWords
  apply first_crystal_time_window_injective hModes
  change crystalTimeWord modes depth left = crystalTimeWord modes depth right
  rw [← future_readout_word_eq_crystal_time_word,
    ← future_readout_word_eq_crystal_time_word]
  exact hWords

/-- Once the depth word is injective, the word with one additional coordinate
is injective as well. -/
theorem spectral_future_word_succ_injective
    {depth : ℕ} {modes : Fin (depth + 1) → K}
    (hModes : Function.Injective modes) :
    Function.Injective
      (futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
        (depth + 1)) := by
  intro left right hWords
  apply spectral_future_word_injective hModes
  funext time
  have hTime := congrFun hWords time.castSucc
  simpa [futureReadoutWord] using hTime

/-- The repository's canonical observation-stability depth is at most the last
sample required by finite Vandermonde tomography. -/
theorem spectral_observation_stability_depth_le
    {depth : ℕ} {modes : Fin (depth + 1) → K}
    (hModes : Function.Injective modes) :
    observationStabilityDepth (oneStepSpectralUpdate modes) modalSumReadout ≤
      depth := by
  have hDepth := spectral_future_word_injective hModes
  have hSucc := spectral_future_word_succ_injective hModes
  have hStable :
      observationSetoid (oneStepSpectralUpdate modes) modalSumReadout depth =
        observationSetoid (oneStepSpectralUpdate modes) modalSumReadout
          (depth + 1) := by
    apply Setoid.ext
    intro left right
    change
      futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout depth left =
          futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout depth right ↔
        futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
            (depth + 1) left =
          futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
            (depth + 1) right
    constructor
    · intro h
      have hEq := hDepth h
      subst right
      rfl
    · intro h
      have hEq := hSucc h
      subst right
      rfl
  unfold observationStabilityDepth
  exact Nat.sInf_le hStable

#print axioms spectral_future_word_injective
#print axioms spectral_future_word_succ_injective
#print axioms spectral_observation_stability_depth_le

end D5.S3.ObserverMemory.FourierFibers.SpectralObservationStabilityDepthBound
