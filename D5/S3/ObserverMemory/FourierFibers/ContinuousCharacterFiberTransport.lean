/- GID: D5/S3/ObserverMemory/FourierFibers/ContinuousCharacterFiberTransport
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/ContinuousCharacterFiberTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit-time samples of continuous Fourier characters generate the existing discrete diagonal spectral-fiber transport. -/

import D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
import D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport
import Mathlib.Tactic

/-!
The continuous Fourier owner supplies the characters `exp (-i t omega)`. The
spectral-fiber owner supplies discrete diagonal transport by powers of modal
multipliers. Sampling each character at time one identifies the two APIs at
every natural time and identifies the scalar crystal readout with finite
Fourier synthesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.ContinuousCharacterFiberTransport

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
open D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport

/-- Unit-time samples of a finite family of continuous Fourier characters. -/
def sampledFourierModes {n : ℕ}
    (frequency : Fin n → ℝ) : Fin n → ℂ :=
  fun mode => fourierPhase (frequency mode) 1

/-- Natural powers of a unit-time sample recover the same continuous character
at the corresponding natural time. -/
theorem sampled_fourier_mode_pow {n : ℕ}
    (frequency : Fin n → ℝ) (mode : Fin n) (time : ℕ) :
    sampledFourierModes frequency mode ^ time =
      fourierPhase (frequency mode) time := by
  unfold sampledFourierModes fourierPhase
  rw [Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Every sampled modal multiplier lies on the unit circle. -/
theorem sampled_fourier_mode_norm_one {n : ℕ}
    (frequency : Fin n → ℝ) (mode : Fin n) :
    ‖sampledFourierModes frequency mode‖ = 1 := by
  simp [sampledFourierModes, fourierPhase, Complex.norm_exp, Complex.mul_re]

/-- Existing discrete spectral transport is pointwise multiplication by the
continuous time character evaluated at the elapsed natural time. -/
theorem spectral_fiber_transport_eq_fourier_character {n : ℕ}
    (frequency : Fin n → ℝ) (time : ℕ) (amplitudes : Fin n → ℂ) :
    spectralFiberTransport (sampledFourierModes frequency) time amplitudes =
      fun mode => amplitudes mode * fourierPhase (frequency mode) time := by
  funext mode
  rw [spectralFiberTransport, sampled_fourier_mode_pow]

/-- The scalar crystal time sample is finite Fourier synthesis at the same
natural time. -/
theorem crystal_time_sample_eq_finite_fourier_synthesis {n : ℕ}
    (frequency : Fin n → ℝ) (amplitudes : Fin n → ℂ) (time : ℕ) :
    crystalTimeSample (sampledFourierModes frequency) amplitudes time =
      finiteFourierSynthesis amplitudes frequency time := by
  classical
  unfold crystalTimeSample finiteFourierSynthesis
  apply Finset.sum_congr rfl
  intro mode _
  rw [sampled_fourier_mode_pow]

/-- Continuous character evaluation and discrete diagonal fiber transport are
the same finite spectral mechanism after unit-time sampling. -/
theorem continuous_character_fiber_transport {n : ℕ}
    (frequency : Fin n → ℝ) (amplitudes : Fin n → ℂ) (time : ℕ) :
    (∀ mode, ‖sampledFourierModes frequency mode‖ = 1) ∧
    spectralFiberTransport (sampledFourierModes frequency) time amplitudes =
      fun mode => amplitudes mode * fourierPhase (frequency mode) time ∧
    crystalTimeSample (sampledFourierModes frequency) amplitudes time =
      finiteFourierSynthesis amplitudes frequency time :=
  ⟨sampled_fourier_mode_norm_one frequency,
    spectral_fiber_transport_eq_fourier_character frequency time amplitudes,
    crystal_time_sample_eq_finite_fourier_synthesis frequency amplitudes time⟩

#print axioms sampled_fourier_mode_pow
#print axioms sampled_fourier_mode_norm_one
#print axioms spectral_fiber_transport_eq_fourier_character
#print axioms crystal_time_sample_eq_finite_fourier_synthesis
#print axioms continuous_character_fiber_transport

end D5.S3.ObserverMemory.FourierFibers.ContinuousCharacterFiberTransport
