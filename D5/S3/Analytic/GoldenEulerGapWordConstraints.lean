/- GID: D5/S3/Analytic/GoldenEulerGapWordConstraints
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The deterministic golden Euler gap word forbids two short steps and three long steps, with the same constraints inherited by Euler phase letters. -/

import D5.S1.Words.Powers.GoldenDesubstitution
import D5.S3.Observer.GoldenPrimeCircle.GoldenEulerStepPhaseLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenEulerGapWordConstraints

open D5.S0.Conventions
open D5.S1.Words
open D5.S1.Words.Powers
open D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfFrequencyBridge
open D5.S3.Observer.GoldenPrimeCircle.GoldenEulerStepPhaseLaw

/-- Compatibility name for the phase of the consecutive golden layer gap. -/
def layerGapPhase
    (time : ℝ) (prime : Nat.Primes) (layer : ℕ) : ℂ :=
  primeStepPhase time prime layer

/-- The short member of the deterministic prime-scaled phase alphabet. -/
def shortStepPhase (time : ℝ) (prime : Nat.Primes) : ℂ :=
  Complex.exp
    (((time * (Real.goldenRatio * Real.log (prime : ℝ)) : ℝ) : ℂ) *
      Complex.I)

/-- The long member of the deterministic prime-scaled phase alphabet. -/
def longStepPhase (time : ℝ) (prime : Nat.Primes) : ℂ :=
  Complex.exp
    (((time *
      (Real.goldenRatio ^ 2 * Real.log (prime : ℝ)) : ℝ) : ℂ) *
      Complex.I)

/-- The current Euler phase law supplies the compatibility bridge used by the
forbidden-word statements below. -/
theorem zeckendorf_selects_layer_gap_phase
    (time : ℝ) (prime : Nat.Primes) (layer : ℕ) :
    (2 ∉ wdigits layer →
      layerGapPhase time prime layer = longStepPhase time prime) ∧
    (2 ∈ wdigits layer →
      layerGapPhase time prime layer = shortStepPhase time prime) := by
  simpa [layerGapPhase, longStepPhase, shortStepPhase] using
    zeckendorf_selects_prime_step_phase time prime layer

/-- A true golden-word letter selects the long `phi^2 log p` frequency gap. -/
theorem golden_true_selects_long_frequency
    (prime : Nat.Primes) {layer : ℕ}
    (hlong : goldenWord layer = true) :
    primeLayerFrequency prime (layer + 1) -
        primeLayerFrequency prime layer =
      Real.goldenRatio ^ 2 * Real.log (prime : ℝ) := by
  have habsent : 2 ∉ wdigits layer :=
    (goldenWord_char_zeckendorf layer).mp hlong
  exact
    (zeckendorf_selects_prime_frequency_gap prime layer).1 habsent

/-- A false golden-word letter selects the short `phi log p` frequency gap. -/
theorem golden_false_selects_short_frequency
    (prime : Nat.Primes) {layer : ℕ}
    (hshort : goldenWord layer = false) :
    primeLayerFrequency prime (layer + 1) -
        primeLayerFrequency prime layer =
      Real.goldenRatio * Real.log (prime : ℝ) := by
  have hpresent : 2 ∈ wdigits layer := by
    by_contra habsent
    have htrue : goldenWord layer = true :=
      (goldenWord_char_zeckendorf layer).mpr habsent
    rw [hshort] at htrue
    exact Bool.noConfusion htrue
  exact
    (zeckendorf_selects_prime_frequency_gap prime layer).2 hpresent

/-- A short frequency step is always followed by a long one. Thus the golden
Euler frequency word has no two consecutive short letters. -/
theorem short_frequency_forces_next_long
    (prime : Nat.Primes) {layer : ℕ}
    (hshort : goldenWord layer = false) :
    (primeLayerFrequency prime (layer + 1) -
          primeLayerFrequency prime layer =
        Real.goldenRatio * Real.log (prime : ℝ)) ∧
      (primeLayerFrequency prime (layer + 2) -
          primeLayerFrequency prime (layer + 1) =
        Real.goldenRatio ^ 2 * Real.log (prime : ℝ)) := by
  constructor
  · exact golden_false_selects_short_frequency prime hshort
  · have hnext : goldenWord (layer + 1) = true :=
      golden_no_two_false hshort
    simpa [Nat.add_assoc] using
      golden_true_selects_long_frequency prime hnext

/-- Two consecutive long frequency steps force the third step to be short.
Thus the golden Euler frequency word has no three consecutive long letters. -/
theorem two_long_frequencies_force_next_short
    (prime : Nat.Primes) {layer : ℕ}
    (hfirst : goldenWord layer = true)
    (hsecond : goldenWord (layer + 1) = true) :
    primeLayerFrequency prime (layer + 3) -
        primeLayerFrequency prime (layer + 2) =
      Real.goldenRatio * Real.log (prime : ℝ) := by
  have hthird : goldenWord (layer + 2) = false :=
    golden_no_three_true hfirst hsecond
  simpa [Nat.add_assoc] using
    golden_false_selects_short_frequency prime hthird

/-- The forbidden-short-pair law is inherited by the Euler phase letters. -/
theorem short_phase_forces_next_long
    (time : ℝ) (prime : Nat.Primes) {layer : ℕ}
    (hshort : goldenWord layer = false) :
    layerGapPhase time prime layer = shortStepPhase time prime ∧
      layerGapPhase time prime (layer + 1) = longStepPhase time prime := by
  have hpresent : 2 ∈ wdigits layer := by
    by_contra habsent
    have htrue : goldenWord layer = true :=
      (goldenWord_char_zeckendorf layer).mpr habsent
    rw [hshort] at htrue
    exact Bool.noConfusion htrue
  have hnext : goldenWord (layer + 1) = true :=
    golden_no_two_false hshort
  have hnextAbsent : 2 ∉ wdigits (layer + 1) :=
    (goldenWord_char_zeckendorf (layer + 1)).mp hnext
  exact
    ⟨(zeckendorf_selects_layer_gap_phase time prime layer).2 hpresent,
      (zeckendorf_selects_layer_gap_phase time prime (layer + 1)).1
        hnextAbsent⟩

/-- The forbidden-long-triple law is likewise inherited by the Euler phase
alphabet before scalar endpoint multiplication forgets chronology. -/
theorem two_long_phases_force_next_short
    (time : ℝ) (prime : Nat.Primes) {layer : ℕ}
    (hfirst : goldenWord layer = true)
    (hsecond : goldenWord (layer + 1) = true) :
    layerGapPhase time prime (layer + 2) =
      shortStepPhase time prime := by
  have hthird : goldenWord (layer + 2) = false :=
    golden_no_three_true hfirst hsecond
  have hpresent : 2 ∈ wdigits (layer + 2) := by
    by_contra habsent
    have htrue : goldenWord (layer + 2) = true :=
      (goldenWord_char_zeckendorf (layer + 2)).mpr habsent
    rw [hthird] at htrue
    exact Bool.noConfusion htrue
  exact
    (zeckendorf_selects_layer_gap_phase time prime (layer + 2)).2
      hpresent

#print axioms golden_true_selects_long_frequency
#print axioms golden_false_selects_short_frequency
#print axioms short_frequency_forces_next_long
#print axioms two_long_frequencies_force_next_short
#print axioms short_phase_forces_next_long
#print axioms two_long_phases_force_next_short

end D5.S3.Analytic.GoldenEulerGapWordConstraints
