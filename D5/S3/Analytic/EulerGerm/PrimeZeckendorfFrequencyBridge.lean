/- GID: D5/S3/Analytic/EulerGerm/PrimeZeckendorfFrequencyBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeckendorf long-short steps become prime-scaled frequency gaps through the golden heat spectrum. -/

import D5.S3.Analytic.EulerGerm.ZeckendorfGoldenBetaGapBridge
import D5.S3.Midline.GoldenHeatSpectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.EulerGerm.PrimeZeckendorfFrequencyBridge

open D5.S0.Conventions
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.ZeckendorfGoldenBetaGapBridge
open D5.S3.Midline.GoldenHeatSpectrum

/-- The real frequency, or heat energy, of one prime-local golden layer. -/
def primeLayerFrequency (prime : Nat.Primes) (layer : ℕ) : ℝ :=
  o5Beta layer * Real.log (prime : ℝ)

/-- A consecutive prime-local frequency gap separates into the golden layer
gap and the logarithmic prime scale. -/
theorem prime_layer_frequency_gap (prime : Nat.Primes) (layer : ℕ) :
    primeLayerFrequency prime (layer + 1) - primeLayerFrequency prime layer =
      (o5Beta (layer + 1) - o5Beta layer) * Real.log (prime : ℝ) := by
  unfold primeLayerFrequency
  ring

/-- The least Zeckendorf digit selects the long or short frequency increment
inside every fixed prime channel. -/
theorem zeckendorf_selects_prime_frequency_gap
    (prime : Nat.Primes) (layer : ℕ) :
    (2 ∉ wdigits layer →
      primeLayerFrequency prime (layer + 1) - primeLayerFrequency prime layer =
        Real.goldenRatio ^ 2 * Real.log (prime : ℝ)) ∧
    (2 ∈ wdigits layer →
      primeLayerFrequency prime (layer + 1) - primeLayerFrequency prime layer =
        Real.goldenRatio * Real.log (prime : ℝ)) := by
  rcases zeckendorf_selects_golden_beta_gap layer with ⟨longStep, shortStep⟩
  constructor
  · intro digitAbsent
    rw [prime_layer_frequency_gap, longStep digitAbsent]
  · intro digitPresent
    rw [prime_layer_frequency_gap, shortStep digitPresent]

/-- Every consecutive prime-local frequency increment is one of the two
Zeckendorf-selected logarithmically scaled golden steps. -/
theorem prime_frequency_gap_dichotomy
    (prime : Nat.Primes) (layer : ℕ) :
    primeLayerFrequency prime (layer + 1) - primeLayerFrequency prime layer =
        Real.goldenRatio ^ 2 * Real.log (prime : ℝ) ∨
      primeLayerFrequency prime (layer + 1) - primeLayerFrequency prime layer =
        Real.goldenRatio * Real.log (prime : ℝ) := by
  classical
  by_cases digitPresent : 2 ∈ wdigits layer
  · exact Or.inr
      ((zeckendorf_selects_prime_frequency_gap prime layer).2 digitPresent)
  · exact Or.inl
      ((zeckendorf_selects_prime_frequency_gap prime layer).1 digitPresent)

/-- Different prime channels carry the same golden layer increment, scaled by
their logarithmic prime coordinates. -/
theorem cross_prime_frequency_gap_balance
    (first second : Nat.Primes) (layer : ℕ) :
    Real.log (second : ℝ) *
        (primeLayerFrequency first (layer + 1) -
          primeLayerFrequency first layer) =
      Real.log (first : ℝ) *
        (primeLayerFrequency second (layer + 1) -
          primeLayerFrequency second layer) := by
  rw [prime_layer_frequency_gap, prime_layer_frequency_gap]
  ring

/-- The frozen excited golden heat spectrum is the prime-local frequency with
its layer coordinate shifted past the vacuum mode. -/
@[simp] theorem golden_spectrum_eq_prime_layer_frequency
    (prime : Nat.Primes) (index : ℕ) :
    goldenSpectrum (prime, index) = primeLayerFrequency prime (index + 1) :=
  rfl

/-- In the frozen excited heat spectrum, the Zeckendorf address of `index + 1`
selects the next prime-scaled long or short frequency gap. -/
theorem zeckendorf_selects_golden_spectrum_gap
    (prime : Nat.Primes) (index : ℕ) :
    (2 ∉ wdigits (index + 1) →
      goldenSpectrum (prime, index + 1) - goldenSpectrum (prime, index) =
        Real.goldenRatio ^ 2 * Real.log (prime : ℝ)) ∧
    (2 ∈ wdigits (index + 1) →
      goldenSpectrum (prime, index + 1) - goldenSpectrum (prime, index) =
        Real.goldenRatio * Real.log (prime : ℝ)) := by
  simpa only [golden_spectrum_eq_prime_layer_frequency] using
    zeckendorf_selects_prime_frequency_gap prime (index + 1)

/-- The common first excited mode in every prime channel has frequency
`phi^2 * log p`, the real-energy form of the first zeta-normalized mode. -/
theorem first_excited_prime_frequency (prime : Nat.Primes) :
    goldenSpectrum (prime, 0) =
      Real.goldenRatio ^ 2 * Real.log (prime : ℝ) := by
  rw [goldenSpectrum, o5_beta_power_law.1]

#print axioms prime_layer_frequency_gap
#print axioms zeckendorf_selects_prime_frequency_gap
#print axioms prime_frequency_gap_dichotomy
#print axioms cross_prime_frequency_gap_balance
#print axioms golden_spectrum_eq_prime_layer_frequency
#print axioms zeckendorf_selects_golden_spectrum_gap
#print axioms first_excited_prime_frequency

end D5.S3.Analytic.EulerGerm.PrimeZeckendorfFrequencyBridge
