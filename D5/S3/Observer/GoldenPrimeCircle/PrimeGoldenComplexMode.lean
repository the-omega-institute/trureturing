/- GID: D5/S3/Observer/GoldenPrimeCircle/PrimeGoldenComplexMode
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Real and imaginary coordinates split a golden prime mode. -/

import D5.S3.ObserverMemory.FourierFibers.PrimeZeckendorfTemporalization
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenPrimeCircle.PrimeGoldenComplexMode

open D5.S3.Analytic.EulerGerm.PrimeZeckendorfFrequencyRigidity
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.ObserverMemory.FourierFibers.PrimeZeckendorfTemporalization

/-- The first golden prime mode with a dissipative coordinate `sigma` and an
oscillatory coordinate `time`. -/
def firstGoldenComplexMode
    (sigma time : ℝ) (prime : Nat.Primes) : ℂ :=
  (firstExcitedHeatMultiplier sigma prime : ℂ) *
    firstExcitedPhaseMultiplier time prime

/-- Euler's formula gives the explicit amplitude-phase decomposition. -/
theorem first_golden_complex_mode_euler
    (sigma time : ℝ) (prime : Nat.Primes) :
    firstGoldenComplexMode sigma time prime =
      (Real.exp (-sigma * goldenSpectrum (prime, 0)) : ℂ) *
        ((Real.cos (time * goldenSpectrum (prime, 0)) : ℂ) +
          (Real.sin (time * goldenSpectrum (prime, 0)) : ℂ) * Complex.I) := by
  rw [firstGoldenComplexMode, firstExcitedHeatMultiplier,
    firstExcitedPhaseMultiplier]
  have hcommute :
      Complex.I * ((time * goldenSpectrum (prime, 0) : ℝ) : ℂ) =
        ((time * goldenSpectrum (prime, 0) : ℝ) : ℂ) * Complex.I := by
    ring
  rw [← Complex.ofReal_mul, hcommute]
  simp [Complex.exp_ofReal_mul_I]

/-- The modulus forgets phase and retains exactly the heat amplitude. -/
@[simp] theorem first_golden_complex_mode_norm
    (sigma time : ℝ) (prime : Nat.Primes) :
    ‖firstGoldenComplexMode sigma time prime‖ =
      firstExcitedHeatMultiplier sigma prime := by
  rw [firstGoldenComplexMode, norm_mul]
  simp [firstExcitedHeatMultiplier, firstExcitedPhaseMultiplier,
    Complex.norm_exp, abs_of_pos (Real.exp_pos _)]

/-- Any positive real coordinate preserves prime identity in the full complex
mode because its modulus is the injective heat readout. -/
theorem first_golden_complex_mode_injective_of_pos
    (sigma time : ℝ) (hsigma : 0 < sigma) :
    Function.Injective (firstGoldenComplexMode sigma time) := by
  intro first second hmode
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hmode
  have hheat :
      firstExcitedHeatMultiplier sigma first =
        firstExcitedHeatMultiplier sigma second := by
    simpa using hnorm
  exact first_excited_heat_multiplier_injective sigma hsigma hheat

/-- On the pure imaginary axis, every prime mode has unit modulus. -/
@[simp] theorem first_golden_complex_mode_zero_sigma_norm
    (time : ℝ) (prime : Nat.Primes) :
    ‖firstGoldenComplexMode 0 time prime‖ = 1 := by
  simp

/-- Pure-phase finite prime vectors return arbitrarily close to coherence at
arbitrarily late times. -/
theorem finite_zero_sigma_complex_mode_recurrence
    (primes : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) (bound : ℝ) :
    ∃ time : ℝ, bound < time ∧ ∀ prime ∈ primes,
      ‖firstGoldenComplexMode 0 time prime - 1‖ < ε := by
  simpa [firstGoldenComplexMode] using
    finite_first_excited_phase_recurrence primes hε bound

/-- Real and imaginary coordinates separate two observational roles: positive
damping is prime-faithful, while pure phase admits finite-channel recurrence. -/
theorem complex_mode_amplitude_phase_dichotomy
    (sigma : ℝ) (hsigma : 0 < sigma)
    (primes : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε)
    (bound phaseTime : ℝ) :
    Function.Injective (firstGoldenComplexMode sigma phaseTime) ∧
      ∃ time : ℝ, bound < time ∧ ∀ prime ∈ primes,
        ‖firstGoldenComplexMode 0 time prime - 1‖ < ε :=
  ⟨first_golden_complex_mode_injective_of_pos sigma phaseTime hsigma,
    finite_zero_sigma_complex_mode_recurrence primes hε bound⟩

#print axioms first_golden_complex_mode_euler
#print axioms first_golden_complex_mode_norm
#print axioms first_golden_complex_mode_injective_of_pos
#print axioms first_golden_complex_mode_zero_sigma_norm
#print axioms finite_zero_sigma_complex_mode_recurrence
#print axioms complex_mode_amplitude_phase_dichotomy

end D5.S3.Observer.GoldenPrimeCircle.PrimeGoldenComplexMode
