/- GID: D5/S3/ObserverMemory/FourierFibers/PrimeZeckendorfTemporalization
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive heat time preserves first-mode prime identity, while wrapped phase time has arbitrarily late finite-channel recurrence. -/

import D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfFrequencyRigidity
import D5.S3.Weil.PrimeAddress.FinitePrimePhaseRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.PrimeZeckendorfTemporalization

open scoped BigOperators
open D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfFrequencyBridge
open D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfFrequencyRigidity
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.Weil.PrimeAddress.FinitePrimePhaseRecurrence

/-- Dissipative temporalization of the first prime-local golden frequency. -/
def firstExcitedHeatMultiplier (time : ℝ) (prime : Nat.Primes) : ℝ :=
  Real.exp (-time * goldenSpectrum (prime, 0))

/-- Oscillatory temporalization of the same frequency on the complex unit
circle. -/
def firstExcitedPhaseMultiplier (time : ℝ) (prime : Nat.Primes) : ℂ :=
  Complex.exp (Complex.I * (time * goldenSpectrum (prime, 0)))

/-- Every positive heat time preserves the identity of the prime channel. -/
theorem first_excited_heat_multiplier_injective
    (time : ℝ) (htime : 0 < time) :
    Function.Injective (firstExcitedHeatMultiplier time) := by
  intro first second hmultiplier
  have hexponent :
      -time * goldenSpectrum (first, 0) =
        -time * goldenSpectrum (second, 0) :=
    Real.exp_injective hmultiplier
  have hfrequency :
      goldenSpectrum (first, 0) = goldenSpectrum (second, 0) := by
    nlinarith
  exact first_excited_frequency_injective hfrequency

/-- Equality after positive heat evolution is exactly equality of prime
channels. -/
theorem first_excited_heat_multiplier_eq_iff
    (time : ℝ) (htime : 0 < time) (first second : Nat.Primes) :
    firstExcitedHeatMultiplier time first =
        firstExcitedHeatMultiplier time second ↔
      first = second := by
  constructor
  · intro hmultiplier
    exact first_excited_heat_multiplier_injective time htime hmultiplier
  · rintro rfl
    rfl

/-- At time zero both temporalizations forget every prime frequency. -/
@[simp] theorem first_excited_temporalizations_zero (prime : Nat.Primes) :
    firstExcitedHeatMultiplier 0 prime = 1 ∧
      firstExcitedPhaseMultiplier 0 prime = 1 := by
  simp [firstExcitedHeatMultiplier, firstExcitedPhaseMultiplier]

/-- For every finite set of prime channels, the wrapped first-mode phase vector
returns arbitrarily close to the coherent phase at arbitrarily late times. -/
theorem finite_first_excited_phase_recurrence
    (primes : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) (bound : ℝ) :
    ∃ time : ℝ, bound < time ∧ ∀ prime ∈ primes,
      ‖firstExcitedPhaseMultiplier time prime - 1‖ < ε := by
  have hscale : 0 < Real.goldenRatio ^ 2 :=
    sq_pos_of_pos Real.goldenRatio_pos
  obtain ⟨ξ, hξ, hclose⟩ :=
    finite_prime_phase_recurrence primes hε
      (bound * Real.goldenRatio ^ 2)
  refine ⟨ξ / Real.goldenRatio ^ 2, ?_, ?_⟩
  · exact (lt_div_iff₀ hscale).2 hξ
  · intro prime hprime
    have hargument :
        (ξ / Real.goldenRatio ^ 2) *
            (Real.goldenRatio ^ 2 * Real.log (prime : ℕ)) =
          ξ * Real.log (prime : ℕ) := by
      field_simp [ne_of_gt hscale]
    unfold firstExcitedPhaseMultiplier
    rw [first_excited_prime_frequency]
    rw [show ((ξ / Real.goldenRatio ^ 2 : ℝ) : Complex) *
        ((Real.goldenRatio ^ 2 * Real.log (prime : ℕ) : ℝ) : Complex) =
        ((ξ : ℝ) : Complex) * ((Real.log (prime : ℕ) : ℝ) : Complex) by
      rw [← Complex.ofReal_mul, hargument, Complex.ofReal_mul]]
    exact hclose prime hprime

/-- A positive heat observer and a wrapped phase observer therefore have
opposite finite-channel behavior: the first is pointwise prime-faithful, while
the second admits arbitrarily late near-coherence. -/
theorem heat_phase_temporalization_dichotomy
    (heatTime : ℝ) (hheatTime : 0 < heatTime)
    (primes : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε)
    (bound : ℝ) :
    Function.Injective (firstExcitedHeatMultiplier heatTime) ∧
      ∃ phaseTime : ℝ, bound < phaseTime ∧ ∀ prime ∈ primes,
        ‖firstExcitedPhaseMultiplier phaseTime prime - 1‖ < ε :=
  ⟨first_excited_heat_multiplier_injective heatTime hheatTime,
    finite_first_excited_phase_recurrence primes hε bound⟩

#print axioms first_excited_heat_multiplier_injective
#print axioms first_excited_heat_multiplier_eq_iff
#print axioms first_excited_temporalizations_zero
#print axioms finite_first_excited_phase_recurrence
#print axioms heat_phase_temporalization_dichotomy

end D5.S3.ObserverMemory.FourierFibers.PrimeZeckendorfTemporalization
