/- GID: D5/S3/Observer/Chronology/PrimeGoldenBidegreeFrequencyRigidity
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: In one prime channel, the irrational golden frequency weight faithfully recovers both prime-event count and short-step count. -/

import D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature
import D5.S1.Phase.Basic
import Mathlib.Tactic

/-!
# Prime-golden bidegree frequency rigidity

For a fixed prime channel, the scalar frequency carried by a bidegree `(k,s)`
is `(k * phi^2 - s) * log p`. The logarithmic factor is nonzero, and the
irrationality of `phi` prevents two different natural-number pairs from having
the same unscaled weight. The complete real frequency therefore recovers both
counting coordinates, while retaining no claim about their chronological order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeGoldenBidegreeFrequencyRigidity

open D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
open D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature

noncomputable section

/-- The prime-independent irrational weight of a prime-golden bidegree. -/
def goldenBidegreeWeight (degree : PrimeGoldenBidegree) : Real :=
  (degree.factorDegree : Real) * Real.goldenRatio ^ 2 -
    (degree.shortStepDegree : Real)

private theorem prime_log_ne_zero (prime : Nat.Primes) :
    Real.log ((prime : Nat) : Real) ≠ 0 := by
  exact ne_of_gt (Real.log_pos (by exact_mod_cast prime.property.one_lt))

/-- Irrationality of the golden ratio makes the unscaled bidegree weight
faithful on natural-number pairs. -/
theorem golden_bidegree_weight_injective :
    Function.Injective goldenBidegreeWeight := by
  intro left right hweight
  have hFactor : left.factorDegree = right.factorDegree := by
    by_contra hne
    let denominator : Int :=
      (left.factorDegree : Int) - (right.factorDegree : Int)
    let numerator : Int :=
      (left.shortStepDegree : Int) -
        (right.shortStepDegree : Int) - denominator
    have hdenominator : denominator ≠ 0 := by
      intro hzero
      apply hne
      have hcast :
          (left.factorDegree : Int) =
            (right.factorDegree : Int) := by
        exact sub_eq_zero.mp (by simpa [denominator] using hzero)
      exact_mod_cast hcast
    have hratio :
        Real.goldenRatio =
          (numerator : Real) / (denominator : Real) := by
      apply (eq_div_iff (Int.cast_ne_zero.mpr hdenominator)).2
      dsimp [goldenBidegreeWeight] at hweight
      rw [Real.goldenRatio_sq] at hweight
      dsimp [numerator, denominator]
      push_cast
      nlinarith
    exact Real.goldenRatio_irrational.ne_rational
      numerator denominator hratio
  have hShort : left.shortStepDegree = right.shortStepDegree := by
    have hshortReal :
        (left.shortStepDegree : Real) =
          (right.shortStepDegree : Real) := by
      dsimp [goldenBidegreeWeight] at hweight
      rw [hFactor] at hweight
      linarith
    exact_mod_cast hshortReal
  apply PrimeGoldenBidegree.ext
  · exact hFactor
  · exact hShort

/-- Multiplication by the nonzero logarithmic prime scale preserves the
faithfulness of the golden bidegree weight. -/
theorem bidegree_frequency_injective (prime : Nat.Primes) :
    Function.Injective (bidegreeFrequency prime) := by
  intro left right hfrequency
  apply golden_bidegree_weight_injective
  change
    goldenBidegreeWeight left * Real.log ((prime : Nat) : Real) =
      goldenBidegreeWeight right * Real.log ((prime : Nat) : Real)
    at hfrequency
  exact mul_right_cancel₀ (prime_log_ne_zero prime) hfrequency

/-- Equality of total frequencies for two words in one prime channel forces
equality of their two counting ledgers. -/
theorem single_prime_total_frequency_recovers_bidegree
    (prime : Nat.Primes)
    (left right : List PrimeGoldenStepEvent)
    (hLeft : IsSinglePrimeWord prime left)
    (hRight : IsSinglePrimeWord prime right)
    (hfrequency : totalStepFrequency left = totalStepFrequency right) :
    primeGoldenBidegree left = primeGoldenBidegree right := by
  apply bidegree_frequency_injective prime
  calc
    bidegreeFrequency prime (primeGoldenBidegree left) =
        totalStepFrequency left :=
      (total_step_frequency_eq_bidegree_of_single_prime
        prime left hLeft).symm
    _ = totalStepFrequency right := hfrequency
    _ = bidegreeFrequency prime (primeGoldenBidegree right) :=
      total_step_frequency_eq_bidegree_of_single_prime
        prime right hRight

/-- The real frequency recovers the count ledger in a fixed prime channel. -/
theorem prime_golden_bidegree_frequency_rigidity
    (prime : Nat.Primes) :
    Function.Injective (bidegreeFrequency prime) ∧
      ∀ left right : List PrimeGoldenStepEvent,
        IsSinglePrimeWord prime left →
        IsSinglePrimeWord prime right →
        totalStepFrequency left = totalStepFrequency right →
        primeGoldenBidegree left = primeGoldenBidegree right :=
  ⟨bidegree_frequency_injective prime,
    single_prime_total_frequency_recovers_bidegree prime⟩

#print axioms golden_bidegree_weight_injective
#print axioms bidegree_frequency_injective
#print axioms single_prime_total_frequency_recovers_bidegree
#print axioms prime_golden_bidegree_frequency_rigidity

end

end D5.S3.Observer.Chronology.PrimeGoldenBidegreeFrequencyRigidity
