/- GID: D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfFrequencyRigidity
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Calibrated golden frequency removes prime relabeling and is rationally independent across primes. -/

import D5.S3.Analytic.PrimeZeckendorf.PrimeRelabelingUnderdetermination
import D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfFrequencyBridge
import D5.S3.Weil.PrimeAddress.PrimeLogIndependence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfFrequencyRigidity

open scoped BigOperators
open D5.S0.Conventions
open D5.S3.Analytic.PrimeZeckendorf.PrimeRelabelingUnderdetermination
open D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfCoordinates
open D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfFrequencyBridge
open D5.S3.Midline.GoldenHeatSpectrum

private theorem prime_real_pos (prime : Nat.Primes) :
    0 < (prime : ℝ) := by
  exact_mod_cast prime.prop.pos

/-- The calibrated first excited frequency, viewed as an observation of a
prime-local golden coordinate. It deliberately ignores the layer coordinate. -/
def firstExcitedFrequencyReadout : PrimeGoldenCoordinate → ℝ :=
  fun state => goldenSpectrum (state.1, 0)

/-- The first excited golden frequency identifies its prime channel. -/
theorem first_excited_frequency_injective :
    Function.Injective
      (fun prime : Nat.Primes => goldenSpectrum (prime, 0)) := by
  intro first second hfrequency
  change goldenSpectrum (first, 0) = goldenSpectrum (second, 0) at hfrequency
  rw [first_excited_prime_frequency,
    first_excited_prime_frequency] at hfrequency
  have hscale : 0 < Real.goldenRatio ^ 2 :=
    sq_pos_of_pos Real.goldenRatio_pos
  have hlog : Real.log (first : ℝ) = Real.log (second : ℝ) := by
    nlinarith
  apply Subtype.ext
  have hreal : (first : ℝ) = (second : ℝ) := by
    calc
      (first : ℝ) = Real.exp (Real.log (first : ℝ)) :=
        (Real.exp_log (prime_real_pos first)).symm
      _ = Real.exp (Real.log (second : ℝ)) := by rw [hlog]
      _ = (second : ℝ) := Real.exp_log (prime_real_pos second)
  exact_mod_cast hreal

/-- Equality of calibrated first frequencies is exactly equality of prime
channels. -/
theorem first_excited_frequency_eq_iff
    (first second : Nat.Primes) :
    goldenSpectrum (first, 0) = goldenSpectrum (second, 0) ↔
      first = second := by
  constructor
  · intro hfrequency
    exact first_excited_frequency_injective hfrequency
  · rintro rfl
    rfl

/-- The first-frequency observer is blind to golden depth inside a fixed prime
channel. -/
@[simp] theorem first_excited_frequency_layer_blind
    (prime : Nat.Primes) (firstLayer secondLayer : ℕ) :
    firstExcitedFrequencyReadout (prime, firstLayer) =
      firstExcitedFrequencyReadout (prime, secondLayer) :=
  rfl

/-- Invariance of the calibrated first-frequency observer forces every prime
relabeling to be the identity. -/
theorem first_excited_frequency_separates_prime_relabelings :
    SeparatesPrimeRelabelings firstExcitedFrequencyReadout := by
  intro relabel hinvariant prime
  have hfrequency := hinvariant (prime, 0)
  change goldenSpectrum (relabel prime, 0) =
    goldenSpectrum (prime, 0) at hfrequency
  exact first_excited_frequency_injective hfrequency

/-- Every genuinely nonidentity prime relabeling is detected by the calibrated
first-frequency observer on a concrete layer-zero state. -/
theorem nontrivial_prime_relabeling_detected_by_frequency
    (relabel : Nat.Primes ≃ Nat.Primes)
    (hnontrivial : ∃ prime, relabel prime ≠ prime) :
    ∃ state : PrimeGoldenCoordinate,
      firstExcitedFrequencyReadout (primeRelabeling relabel state) ≠
        firstExcitedFrequencyReadout state := by
  rcases hnontrivial with ⟨prime, hprime⟩
  refine ⟨(prime, 0), ?_⟩
  intro hfrequency
  apply hprime
  apply first_excited_frequency_injective
  simpa [firstExcitedFrequencyReadout] using hfrequency

/-- Calibrated first frequency together with the canonical Zeckendorf address
recovers both coordinates without exposing the raw prime label. -/
def frequencyZeckendorfReadout :
    PrimeGoldenCoordinate → ℝ × WDigitString :=
  fun state =>
    (firstExcitedFrequencyReadout state, wEncoding state.2)

/-- The frequency-Zeckendorf observer is faithful on the complete product
coordinate. -/
theorem frequency_zeckendorf_readout_injective :
    Function.Injective frequencyZeckendorfReadout := by
  intro left right hsame
  apply Prod.ext
  · apply first_excited_frequency_injective
    simpa [frequencyZeckendorfReadout,
      firstExcitedFrequencyReadout] using congrArg Prod.fst hsame
  · have haddress : wEncoding left.2 = wEncoding right.2 := by
      simpa [frequencyZeckendorfReadout] using congrArg Prod.snd hsame
    have hdecoded := congrArg decodeWAddress haddress
    simpa using hdecoded

/-- The complete family of first excited prime frequencies is linearly
independent over the rationals. Hence finite rational superpositions have no
hidden cross-prime cancellation. -/
theorem first_excited_frequency_rational_independence :
    LinearIndependent ℚ
      (fun prime : Nat.Primes => goldenSpectrum (prime, 0)) := by
  rw [linearIndependent_iff']
  intro primes coefficients hsum prime hprime
  have hscaled :
      Real.goldenRatio ^ 2 *
          (∑ p ∈ primes,
            (algebraMap ℚ ℝ) (coefficients p) * Real.log (p : ℝ)) = 0 := by
    calc
      Real.goldenRatio ^ 2 *
          (∑ p ∈ primes,
            (algebraMap ℚ ℝ) (coefficients p) * Real.log (p : ℝ)) =
        ∑ p ∈ primes,
          (algebraMap ℚ ℝ) (coefficients p) *
            (Real.goldenRatio ^ 2 * Real.log (p : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _
              ring
      _ = ∑ p ∈ primes, coefficients p • goldenSpectrum (p, 0) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Algebra.smul_def, first_excited_prime_frequency]
      _ = 0 := hsum
  have hscale : Real.goldenRatio ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos Real.goldenRatio_pos)
  have hlogSum :
      (∑ p ∈ primes,
        (algebraMap ℚ ℝ) (coefficients p) * Real.log (p : ℝ)) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hscale
  have hindependent := linearIndependent_iff'.mp
    D5.S3.Weil.PrimeAddress.PrimeLogIndependence.prime_log_rational_independence
  apply hindependent primes coefficients
  · simpa only [Algebra.smul_def] using hlogSum
  · exact hprime

/-- Explicit finite form of the preceding independence theorem. -/
theorem finite_first_frequency_relation_has_zero_coefficients
    (primes : Finset Nat.Primes) (coefficients : Nat.Primes → ℚ)
    (hsum : ∑ prime ∈ primes,
      coefficients prime • goldenSpectrum (prime, 0) = 0) :
    ∀ prime ∈ primes, coefficients prime = 0 :=
  linearIndependent_iff'.mp first_excited_frequency_rational_independence
    primes coefficients hsum

#print axioms first_excited_frequency_injective
#print axioms first_excited_frequency_eq_iff
#print axioms first_excited_frequency_separates_prime_relabelings
#print axioms nontrivial_prime_relabeling_detected_by_frequency
#print axioms frequency_zeckendorf_readout_injective
#print axioms first_excited_frequency_rational_independence
#print axioms finite_first_frequency_relation_has_zero_coefficients

end D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfFrequencyRigidity
