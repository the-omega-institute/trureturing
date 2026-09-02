/- GID: D5/S3/ObserverMemory/FourierFibers/ContinuousCharacterFiberTransport
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/ContinuousCharacterFiberTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sampling a continuous Fourier character at unit time recovers the diagonal spectral-fiber transport and finite Fourier synthesis at every natural time. -/

import D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
import D5.S3.ObserverMemory.FourierFibers.TimeShiftSpectralFiberTransport

/-!
The continuous Fourier owner already proves that `exp (-i t omega)` is a
unitary additive character. The spectral-fiber owner already proves the power
semigroup law for discrete modal multipliers. This bridge identifies the two:
a mode is the unit-time character value, and its natural powers are exactly the
same character evaluated at natural time.
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

/-- Natural powers of a unit-time Fourier sample are evaluations of the same
character at natural time. -/
theorem sampled_fourier_mode_pow {n : ℕ}
    (frequency : Fin n → ℝ) (mode : Fin n) (time : ℕ) :
    sampledFourierModes frequency mode ^ time =
      fourierPhase (frequency mode) time := by
  unfold sampledFourierModes fourierPhase
  rw [Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The sampled modes retain unit norm. -/
theorem sampled_fourier_mode_norm_one {n : ℕ}
    (frequency : Fin n → ℝ) (mode : Fin n) :
    ‖sampledFourierModes frequency mode‖ = 1 := by
  simpa [sampledFourierModes] using
    (fourier_phase_character_laws (frequency mode) 0 1 0).2.2.2.1

/-- Discrete spectral transport is pointwise multiplication by the continuous
time character evaluated at the elapsed natural time. -/
theorem spectral_fiber_transport_eq_fourier_character {n : ℕ}
    (frequency : Fin n → ℝ) (time : ℕ) (amplitudes : Fin n → ℂ) :
    spectralFiberTransport (sampledFourierModes frequency) time amplitudes =
      fun mode => amplitudes mode * fourierPhase (frequency mode) time := by
  funext mode
  simp only [spectralFiberTransport, sampled_fourier_mode_pow]

/-- The crystal scalar time sample is exactly finite Fourier synthesis at the
same natural time. -/
theorem crystal_time_sample_eq_finite_fourier_synthesis {n : ℕ}
    (frequency : Fin n → ℝ) (amplitudes : Fin n → ℂ) (time : ℕ) :
    crystalTimeSample (sampledFourierModes frequency) amplitudes time =
      finiteFourierSynthesis amplitudes frequency time := by
  classical
  unfold crystalTimeSample finiteFourierSynthesis
  apply Finset.sum_congr rfl
  intro mode _
  rw [sampled_fourier_mode_pow]

/-- Time translation on every finite Fourier fiber is the same character law
viewed through the discrete transport owner. -/
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
