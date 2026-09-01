/- GID: D5/S3/ObserverMemory/FourierFibers/TimeShiftSpectralFiberTransport
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/TimeShiftSpectralFiberTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Time translation becomes diagonal multiplication on spectral fibers and obeys an exact semigroup law. -/

import D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport

open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

universe u

variable {K : Type u} [Field K]

/-- Diagonal transport of modal amplitudes through `steps` units of time. -/
def spectralFiberTransport {n : ℕ}
    (modes : Fin n → K) (steps : ℕ) (amplitudes : Fin n → K) : Fin n → K :=
  fun mode => amplitudes mode * modes mode ^ steps

@[simp] theorem spectral_fiber_transport_zero {n : ℕ}
    (modes amplitudes : Fin n → K) :
    spectralFiberTransport modes 0 amplitudes = amplitudes := by
  funext mode
  simp [spectralFiberTransport]

/-- Successive time transports compose by addition of elapsed time. -/
theorem spectral_fiber_transport_add {n : ℕ}
    (modes : Fin n → K) (first second : ℕ) (amplitudes : Fin n → K) :
    spectralFiberTransport modes second
        (spectralFiberTransport modes first amplitudes) =
      spectralFiberTransport modes (first + second) amplitudes := by
  funext mode
  simp [spectralFiberTransport, pow_add]
  ring

/-- Reading after transport equals reading the original amplitudes at the
translated time. -/
theorem crystal_time_sample_after_transport {n : ℕ}
    (modes amplitudes : Fin n → K) (time shift : ℕ) :
    crystalTimeSample modes (spectralFiberTransport modes shift amplitudes) time =
      crystalTimeSample modes amplitudes (shift + time) := by
  unfold crystalTimeSample spectralFiberTransport
  apply Finset.sum_congr rfl
  intro mode _
  rw [pow_add]
  ring

/-- The time-zero observation after transport is the observation at the
transport depth. -/
theorem transported_zero_sample {n : ℕ}
    (modes amplitudes : Fin n → K) (shift : ℕ) :
    crystalTimeSample modes (spectralFiberTransport modes shift amplitudes) 0 =
      crystalTimeSample modes amplitudes shift := by
  simpa using crystal_time_sample_after_transport modes amplitudes 0 shift

#print axioms spectral_fiber_transport_zero
#print axioms spectral_fiber_transport_add
#print axioms crystal_time_sample_after_transport
#print axioms transported_zero_sample

end D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport
