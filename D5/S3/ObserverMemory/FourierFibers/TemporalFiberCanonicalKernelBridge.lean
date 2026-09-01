/- GID: D5/S3/ObserverMemory/FourierFibers/TemporalFiberCanonicalKernelBridge
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/TemporalFiberCanonicalKernelBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Consecutive finite spectral time fibers are exactly the canonical future-readout kernels. -/

import D5.S3.ObserverMemory.FourierFibers.TemporalFiberObserverUpgrade
import D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge
import D5.S3.Observer.Separation.FiniteObservationRefinementBound

/-!
Library-first audit:
* `futureReadoutWord` and `observationSetoid` are the repository's canonical
  finite-delay readout and equality-kernel APIs.
* `temporalWindowReadout` is reused only as the finite spectral realization.
* This owner proves the bridge between those existing notions and introduces
  no second observation-kernel hierarchy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.TemporalFiberCanonicalKernelBridge

open D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge
open D5.S3.ObserverMemory.FourierFibers.TemporalFiberObserverUpgrade
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.Observer.Separation.FiniteObservationRefinementBound

universe u

variable {K : Type u} [Field K]

/-- Equality on the consecutive temporal window `0, ..., depth` is exactly the
canonical future-readout equivalence relation. -/
theorem same_temporal_fiber_range_iff_observation_setoid
    {n : ℕ} (modes : Fin n → K) (depth : ℕ)
    (left right : Fin n → K) :
    SameTemporalFiber modes (Finset.range (depth + 1)) left right ↔
      (observationSetoid (oneStepSpectralUpdate modes) modalSumReadout depth)
        left right := by
  constructor
  · intro hWindow
    change temporalWindowReadout modes (Finset.range (depth + 1)) left =
      temporalWindowReadout modes (Finset.range (depth + 1)) right at hWindow
    change futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
        depth left =
      futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
        depth right
    rw [future_readout_word_eq_crystal_time_word,
      future_readout_word_eq_crystal_time_word]
    funext time
    have hAt := congrFun hWindow
      ⟨time.1, Finset.mem_range.mpr time.2⟩
    simpa [temporalWindowReadout, crystalTimeWord] using hAt
  · intro hSetoid
    change futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
        depth left =
      futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
        depth right at hSetoid
    rw [future_readout_word_eq_crystal_time_word,
      future_readout_word_eq_crystal_time_word] at hSetoid
    unfold SameTemporalFiber temporalWindowReadout
    funext time
    change crystalTimeSample modes left time.1 =
      crystalTimeSample modes right time.1
    have hTime := congrFun hSetoid
      ⟨time.1, Finset.mem_range.mp time.2⟩
    simpa [crystalTimeWord] using hTime

/-- The equality kernel of the consecutive temporal readout is literally the
canonical observation setoid. -/
theorem temporal_range_kernel_eq_observation_setoid
    {n : ℕ} (modes : Fin n → K) (depth : ℕ) :
    Setoid.ker
        (temporalWindowReadout modes (Finset.range (depth + 1))) =
      observationSetoid (oneStepSpectralUpdate modes) modalSumReadout depth := by
  apply Setoid.ext
  intro left right
  exact same_temporal_fiber_range_iff_observation_setoid modes depth left right

#print axioms same_temporal_fiber_range_iff_observation_setoid
#print axioms temporal_range_kernel_eq_observation_setoid

end D5.S3.ObserverMemory.FourierFibers.TemporalFiberCanonicalKernelBridge
