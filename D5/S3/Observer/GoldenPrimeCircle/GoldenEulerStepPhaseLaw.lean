/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenEulerStepPhaseLaw
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeckendorf golden steps form a two-letter Euler phase alphabet. -/

import D5.S3.Analytic.EulerGerm.PrimeZeckendorfFrequencyBridge
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenEulerStepPhaseLaw

open D5.S0.Conventions
open D5.S3.Analytic.EulerGerm.PrimeZeckendorfFrequencyBridge

/-- The frequency increment carried by one golden Euler step. -/
def primeStepFrequency (prime : Nat.Primes) (layer : ℕ) : ℝ :=
  primeLayerFrequency prime (layer + 1) - primeLayerFrequency prime layer

/-- The unit-circle phase accumulated by one golden Euler step. -/
def primeStepPhase (time : ℝ) (prime : Nat.Primes) (layer : ℕ) : ℂ :=
  Complex.exp
    (((time * primeStepFrequency prime layer : ℝ) : ℂ) * Complex.I)

/-- The least Zeckendorf digit selects the long or short member of the
prime-scaled two-frequency alphabet. -/
theorem prime_step_frequency_zeckendorf
    (prime : Nat.Primes) (layer : ℕ) :
    (2 ∉ wdigits layer →
      primeStepFrequency prime layer =
        Real.goldenRatio ^ 2 * Real.log (prime : ℝ)) ∧
    (2 ∈ wdigits layer →
      primeStepFrequency prime layer =
        Real.goldenRatio * Real.log (prime : ℝ)) := by
  simpa [primeStepFrequency] using
    zeckendorf_selects_prime_frequency_gap prime layer

/-- Euler's formula resolves every deterministic step phase into cosine and
sine coordinates. -/
theorem prime_step_phase_euler
    (time : ℝ) (prime : Nat.Primes) (layer : ℕ) :
    primeStepPhase time prime layer =
      (Real.cos (time * primeStepFrequency prime layer) : ℂ) +
        (Real.sin (time * primeStepFrequency prime layer) : ℂ) * Complex.I := by
  unfold primeStepPhase
  exact Complex.exp_ofReal_mul_I
    (time * primeStepFrequency prime layer)

/-- Every step phase lies on the complex unit circle. -/
@[simp] theorem prime_step_phase_norm
    (time : ℝ) (prime : Nat.Primes) (layer : ℕ) :
    ‖primeStepPhase time prime layer‖ = 1 := by
  simp [primeStepPhase, Complex.norm_exp]

/-- Zeckendorf selection transports directly from frequency to phase. -/
theorem zeckendorf_selects_prime_step_phase
    (time : ℝ) (prime : Nat.Primes) (layer : ℕ) :
    (2 ∉ wdigits layer →
      primeStepPhase time prime layer =
        Complex.exp
          (((time * (Real.goldenRatio ^ 2 * Real.log (prime : ℝ)) : ℝ) : ℂ) *
            Complex.I)) ∧
    (2 ∈ wdigits layer →
      primeStepPhase time prime layer =
        Complex.exp
          (((time * (Real.goldenRatio * Real.log (prime : ℝ)) : ℝ) : ℂ) *
            Complex.I)) := by
  constructor
  · intro habsent
    rw [primeStepPhase,
      (prime_step_frequency_zeckendorf prime layer).1 habsent]
  · intro hpresent
    rw [primeStepPhase,
      (prime_step_frequency_zeckendorf prime layer).2 hpresent]

/-- Since `phi^2 = phi + 1`, a long-step phase splits into a short golden
rotation and one ordinary prime-log rotation. -/
theorem long_step_phase_factorization
    (time : ℝ) (prime : Nat.Primes) :
    Complex.exp
        (((time * (Real.goldenRatio ^ 2 * Real.log (prime : ℝ)) : ℝ) : ℂ) *
          Complex.I) =
      Complex.exp
          (((time * (Real.goldenRatio * Real.log (prime : ℝ)) : ℝ) : ℂ) *
            Complex.I) *
        Complex.exp
          (((time * Real.log (prime : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  rw [Real.goldenRatio_sq]
  push_cast
  ring

/-- Two step phases compose by adding their deterministic frequency
increments. -/
theorem two_step_phase_additivity
    (time : ℝ) (prime : Nat.Primes) (first second : ℕ) :
    primeStepPhase time prime first * primeStepPhase time prime second =
      Complex.exp
        (((time *
          (primeStepFrequency prime first + primeStepFrequency prime second) : ℝ) : ℂ) *
          Complex.I) := by
  rw [primeStepPhase, primeStepPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A final scalar `U(1)` phase cannot remember the order of two steps. Full
chronology requires time-resolved observation or a noncommutative lift. -/
theorem adjacent_step_order_invisible
    (time : ℝ) (prime : Nat.Primes) (first second : ℕ) :
    primeStepPhase time prime first * primeStepPhase time prime second =
      primeStepPhase time prime second * primeStepPhase time prime first := by
  exact mul_comm _ _

#print axioms prime_step_frequency_zeckendorf
#print axioms prime_step_phase_euler
#print axioms prime_step_phase_norm
#print axioms zeckendorf_selects_prime_step_phase
#print axioms long_step_phase_factorization
#print axioms two_step_phase_additivity
#print axioms adjacent_step_order_invisible

end D5.S3.Observer.GoldenPrimeCircle.GoldenEulerStepPhaseLaw
