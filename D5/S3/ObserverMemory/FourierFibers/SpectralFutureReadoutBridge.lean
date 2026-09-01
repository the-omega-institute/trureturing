/- GID: D5/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The finite spectral time-delay word is exactly the repository's
     canonical future-readout word for diagonal modal transport. -/

import D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport
import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/-!
Library-first note: `futureReadoutWord` is already the canonical finite-delay
observer in Trueturning.  This owner constructs no competing delay-coordinate
API.  It identifies the finite spectral model with that existing truth source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge

open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
open D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

universe u

variable {K : Type u} [Field K]

/-- Scalar readout that sums all modal amplitudes. -/
def modalSumReadout {n : ℕ} (amplitudes : Fin n → K) : K :=
  ∑ mode : Fin n, amplitudes mode

/-- One unit of diagonal modal evolution. -/
def oneStepSpectralUpdate {n : ℕ}
    (modes : Fin n → K) (amplitudes : Fin n → K) : Fin n → K :=
  spectralFiberTransport modes 1 amplitudes

/-- Time samples through a specified finite depth. -/
def crystalTimeWord {n : ℕ}
    (modes : Fin n → K) (depth : ℕ) (amplitudes : Fin n → K) :
    Fin (depth + 1) → K :=
  fun time => crystalTimeSample modes amplitudes time

/-- Iterating the one-step update is exactly transport through that many
spectral steps. -/
theorem one_step_spectral_update_iterate {n : ℕ}
    (modes : Fin n → K) (time : ℕ) (amplitudes : Fin n → K) :
    ((oneStepSpectralUpdate modes)^[time]) amplitudes =
      spectralFiberTransport modes time amplitudes := by
  induction time generalizing amplitudes with
  | zero =>
      simp [oneStepSpectralUpdate]
  | succ time ih =>
      rw [Function.iterate_succ_apply, ih]
      unfold oneStepSpectralUpdate
      rw [spectral_fiber_transport_add]
      simpa [Nat.add_comm]

/-- The spectral delay-coordinate word reuses the canonical future-readout
word without loss or extra assumptions. -/
theorem future_readout_word_eq_crystal_time_word {n : ℕ}
    (modes : Fin n → K) (depth : ℕ) (amplitudes : Fin n → K) :
    futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
        depth amplitudes =
      crystalTimeWord modes depth amplitudes := by
  funext time
  simp only [futureReadoutWord, crystalTimeWord]
  rw [one_step_spectral_update_iterate]
  unfold modalSumReadout spectralFiberTransport crystalTimeSample
  apply Finset.sum_congr rfl
  intro mode _
  ring

/-- At depth `n - 1`, the canonical future word is the same finite time trace
used by Vandermonde tomography whenever the index types coincide. -/
example (modes : Fin 2 → K) (amplitudes : Fin 2 → K) :
    futureReadoutWord (oneStepSpectralUpdate modes) modalSumReadout
        1 amplitudes =
      firstCrystalTimeWindow modes amplitudes := by
  rw [future_readout_word_eq_crystal_time_word]
  rfl

#print axioms one_step_spectral_update_iterate
#print axioms future_readout_word_eq_crystal_time_word

end D5.S3.ObserverMemory.FourierFibers.SpectralFutureReadoutBridge
