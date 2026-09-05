/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenPrimeBeatSecondMagnus
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden long-short frequency difference is log p, giving a prime-specific half-beat time where the second-Magnus slot kernel has maximal norm. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenEulerStepPhaseLaw
import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import Mathlib.Tactic

/-!
# Prime beat times for golden second-Magnus separation

The deterministic golden frequency alphabet in a fixed prime channel is

`phi * log p` and `phi^2 * log p`.

Their difference is exactly `log p`. Hence the relative phase has a canonical
prime-dependent half-beat time `pi / log p` and full-beat time
`2 * pi / log p`. At the half beat, the long and short Fourier characters are
opposite and the alternating second-Magnus slot kernel has norm exactly two,
the global upper bound from `SecondMagnusSwapCurvature`. At the full beat, the
two characters coincide and the slot kernel vanishes.

This gives a calibrated observation window for one prime channel. It does not
supply a common uniform time for infinitely many primes, rule out all other
resonances, construct a continuous Magnus integral, locate zeta zeros, or
prove RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenPrimeBeatSecondMagnus

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature

noncomputable section

/-- The short member of the prime-scaled golden frequency alphabet. -/
def shortGoldenPrimeFrequency (prime : Nat.Primes) : ℝ :=
  Real.goldenRatio * Real.log (prime : ℝ)

/-- The long member of the prime-scaled golden frequency alphabet. -/
def longGoldenPrimeFrequency (prime : Nat.Primes) : ℝ :=
  Real.goldenRatio ^ 2 * Real.log (prime : ℝ)

/-- The positive time at which the relative prime-log phase is `-1`. -/
def goldenPrimeHalfBeatTime (prime : Nat.Primes) : ℝ :=
  Real.pi / Real.log (prime : ℝ)

/-- The time at which the relative prime-log phase completes one full turn. -/
def goldenPrimeFullBeatTime (prime : Nat.Primes) : ℝ :=
  2 * goldenPrimeHalfBeatTime prime

private theorem prime_real_one_lt (prime : Nat.Primes) :
    (1 : ℝ) < (prime : ℝ) := by
  exact_mod_cast prime.prop.one_lt

private theorem prime_log_pos (prime : Nat.Primes) :
    0 < Real.log (prime : ℝ) :=
  Real.log_pos (prime_real_one_lt prime)

private theorem prime_log_ne_zero (prime : Nat.Primes) :
    Real.log (prime : ℝ) ≠ 0 :=
  ne_of_gt (prime_log_pos prime)

/-- The long-short golden frequency gap is the unscaled prime logarithm. -/
@[simp] theorem long_sub_short_frequency (prime : Nat.Primes) :
    longGoldenPrimeFrequency prime - shortGoldenPrimeFrequency prime =
      Real.log (prime : ℝ) := by
  unfold longGoldenPrimeFrequency shortGoldenPrimeFrequency
  rw [Real.goldenRatio_sq]
  ring

/-- Equivalently, the long frequency is the short golden frequency plus one
ordinary prime-log frequency. -/
theorem long_frequency_eq_short_add_log (prime : Nat.Primes) :
    longGoldenPrimeFrequency prime =
      shortGoldenPrimeFrequency prime + Real.log (prime : ℝ) := by
  linarith [long_sub_short_frequency prime]

/-- Every prime channel has a positive half-beat observation time. -/
theorem golden_prime_half_beat_time_pos (prime : Nat.Primes) :
    0 < goldenPrimeHalfBeatTime prime := by
  exact div_pos Real.pi_pos (prime_log_pos prime)

private theorem fourier_phase_at_half_beat
    (frequency : ℝ) (hFrequency : frequency ≠ 0) :
    fourierPhase frequency (Real.pi / frequency) = -1 := by
  unfold fourierPhase
  have hCancel : (Real.pi / frequency) * frequency = Real.pi :=
    div_mul_cancel₀ Real.pi hFrequency
  have hArgument :
      -Complex.I * ((Real.pi / frequency : ℝ) : ℂ) * (frequency : ℂ) =
        -((Real.pi : ℂ) * Complex.I) := by
    calc
      -Complex.I * ((Real.pi / frequency : ℝ) : ℂ) * (frequency : ℂ) =
          -Complex.I *
            ((((Real.pi / frequency) * frequency : ℝ) : ℂ)) := by
        push_cast
        ring
      _ = -Complex.I * (Real.pi : ℂ) := by rw [hCancel]
      _ = -((Real.pi : ℂ) * Complex.I) := by ring
  rw [hArgument]
  exact Complex.exp_neg_pi_mul_I

private theorem fourier_phase_at_full_beat
    (frequency : ℝ) (hFrequency : frequency ≠ 0) :
    fourierPhase frequency (2 * (Real.pi / frequency)) = 1 := by
  calc
    fourierPhase frequency (2 * (Real.pi / frequency)) =
        fourierPhase frequency
          ((Real.pi / frequency) + (Real.pi / frequency)) := by
      congr 1
      ring
    _ = fourierPhase frequency (Real.pi / frequency) *
          fourierPhase frequency (Real.pi / frequency) :=
      (fourier_phase_character_laws frequency 0
        (Real.pi / frequency) (Real.pi / frequency)).2.1
    _ = 1 := by
      rw [fourier_phase_at_half_beat frequency hFrequency]
      norm_num

/-- At the prime half beat, the long Fourier character is the negative of the
short Fourier character. -/
theorem long_phase_eq_neg_short_at_half_beat (prime : Nat.Primes) :
    fourierPhase (longGoldenPrimeFrequency prime)
        (goldenPrimeHalfBeatTime prime) =
      -fourierPhase (shortGoldenPrimeFrequency prime)
        (goldenPrimeHalfBeatTime prime) := by
  rw [long_frequency_eq_short_add_log]
  rw [(fourier_phase_character_laws
    (shortGoldenPrimeFrequency prime) (Real.log (prime : ℝ))
    (goldenPrimeHalfBeatTime prime) 0).2.2.1]
  have hPrimePhase :
      fourierPhase (Real.log (prime : ℝ))
          (goldenPrimeHalfBeatTime prime) = -1 := by
    simpa [goldenPrimeHalfBeatTime] using
      fourier_phase_at_half_beat
        (Real.log (prime : ℝ)) (prime_log_ne_zero prime)
  rw [hPrimePhase]
  ring

/-- At the prime full beat, the long and short Fourier characters coincide. -/
theorem long_phase_eq_short_at_full_beat (prime : Nat.Primes) :
    fourierPhase (longGoldenPrimeFrequency prime)
        (goldenPrimeFullBeatTime prime) =
      fourierPhase (shortGoldenPrimeFrequency prime)
        (goldenPrimeFullBeatTime prime) := by
  rw [long_frequency_eq_short_add_log]
  rw [(fourier_phase_character_laws
    (shortGoldenPrimeFrequency prime) (Real.log (prime : ℝ))
    (goldenPrimeFullBeatTime prime) 0).2.2.1]
  have hPrimePhase :
      fourierPhase (Real.log (prime : ℝ))
          (goldenPrimeFullBeatTime prime) = 1 := by
    simpa [goldenPrimeFullBeatTime, goldenPrimeHalfBeatTime] using
      fourier_phase_at_full_beat
        (Real.log (prime : ℝ)) (prime_log_ne_zero prime)
  rw [hPrimePhase, mul_one]

/-- At time slots zero and the prime half beat, the alternating slot kernel is
exactly minus twice the short-channel phase. -/
theorem second_magnus_kernel_at_prime_half_beat
    (prime : Nat.Primes) :
    secondMagnusSwapKernel
        (shortGoldenPrimeFrequency prime)
        (longGoldenPrimeFrequency prime)
        0 (goldenPrimeHalfBeatTime prime) =
      -2 * fourierPhase (shortGoldenPrimeFrequency prime)
        (goldenPrimeHalfBeatTime prime) := by
  unfold secondMagnusSwapKernel
  rw [long_phase_eq_neg_short_at_half_beat]
  simp [fourierPhase]
  ring

/-- The prime half beat attains the universal norm-two upper bound of the
second-Magnus slot kernel. -/
theorem second_magnus_kernel_prime_half_beat_norm
    (prime : Nat.Primes) :
    ‖secondMagnusSwapKernel
        (shortGoldenPrimeFrequency prime)
        (longGoldenPrimeFrequency prime)
        0 (goldenPrimeHalfBeatTime prime)‖ = 2 := by
  rw [second_magnus_kernel_at_prime_half_beat, norm_mul]
  have hPhaseNorm :
      ‖fourierPhase (shortGoldenPrimeFrequency prime)
          (goldenPrimeHalfBeatTime prime)‖ = 1 :=
    (fourier_phase_character_laws
      (shortGoldenPrimeFrequency prime) 0
      (goldenPrimeHalfBeatTime prime) 0).2.2.2.1
  rw [hPhaseNorm]
  norm_num

/-- In particular, the half-beat second-Magnus coefficient is nonzero. -/
theorem second_magnus_kernel_prime_half_beat_ne_zero
    (prime : Nat.Primes) :
    secondMagnusSwapKernel
        (shortGoldenPrimeFrequency prime)
        (longGoldenPrimeFrequency prime)
        0 (goldenPrimeHalfBeatTime prime) ≠ 0 := by
  intro hZero
  have hNorm := congrArg norm hZero
  rw [second_magnus_kernel_prime_half_beat_norm] at hNorm
  norm_num at hNorm

/-- At the corresponding full beat the two phase channels resonate again and
the alternating slot kernel vanishes. -/
theorem second_magnus_kernel_at_prime_full_beat
    (prime : Nat.Primes) :
    secondMagnusSwapKernel
        (shortGoldenPrimeFrequency prime)
        (longGoldenPrimeFrequency prime)
        0 (goldenPrimeFullBeatTime prime) = 0 := by
  unfold secondMagnusSwapKernel
  rw [long_phase_eq_short_at_full_beat]
  simp [fourierPhase]

/-- The same prime-log gap therefore produces alternating maximal separation
and exact recurrence at its half- and full-beat windows. -/
theorem prime_beat_separation_recurrence
    (prime : Nat.Primes) :
    ‖secondMagnusSwapKernel
        (shortGoldenPrimeFrequency prime)
        (longGoldenPrimeFrequency prime)
        0 (goldenPrimeHalfBeatTime prime)‖ = 2 ∧
      secondMagnusSwapKernel
        (shortGoldenPrimeFrequency prime)
        (longGoldenPrimeFrequency prime)
        0 (goldenPrimeFullBeatTime prime) = 0 :=
  ⟨second_magnus_kernel_prime_half_beat_norm prime,
    second_magnus_kernel_at_prime_full_beat prime⟩

#print axioms long_sub_short_frequency
#print axioms golden_prime_half_beat_time_pos
#print axioms long_phase_eq_neg_short_at_half_beat
#print axioms long_phase_eq_short_at_full_beat
#print axioms second_magnus_kernel_at_prime_half_beat
#print axioms second_magnus_kernel_prime_half_beat_norm
#print axioms second_magnus_kernel_prime_half_beat_ne_zero
#print axioms second_magnus_kernel_at_prime_full_beat
#print axioms prime_beat_separation_recurrence

end

end D5.S3.Observer.GoldenPrimeCircle.GoldenPrimeBeatSecondMagnus
