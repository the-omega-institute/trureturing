/- GID: D5/S3/Observer/Chronology/PrimeGoldenBigradedChronologicalSignature
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-factor degree and golden short-step degree form an additive bigrading preserved by reversal while the chronological signature takes its antipode. -/

import D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
import Mathlib.Tactic

/-!
# Prime-golden bigraded chronological signatures

A finite prime-golden event word carries two additive discrete degrees.

* `factorDegree` counts prime events with multiplicity. Its parity character is
  the Liouville value of the represented prime product.
* `shortStepDegree` counts events whose least occupied Zeckendorf index selects
  the short golden step. Its parity character is the product of the local
  long/short signs.

The two degrees are packaged beside the existing step-two chronological
signature. Concatenation obeys Chen multiplication in the chronological
component and coordinatewise addition in the bidegree. Reverse-and-negate acts
by the Hopf antipode on the chronological component while preserving both
unsigned degrees.

For a word contained in one prime channel, the complete scalar frequency is
recovered from the bidegree as

`(factorDegree * phi^2 - shortStepDegree) * log p`.

Thus the bidegree records the abelian counting information, while the Magnus
coordinate records oriented order. The module does not identify factor parity
with Zeckendorf parity, construct an infinite signature, transport the finite
characters to a zeta quotient, or assert a physical arrow of time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepTwoChronologicalLogarithm
open D5.S3.Observer.Chronology.ChronologicalSignatureHopf
open D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge

noncomputable section

universe u

/-- The two additive degrees carried by a finite prime-golden event word. -/
@[ext]
structure PrimeGoldenBidegree where
  factorDegree : Nat
  shortStepDegree : Nat

/-- Coordinatewise addition of prime and golden degrees. -/
def bidegreeAdd
    (left right : PrimeGoldenBidegree) : PrimeGoldenBidegree where
  factorDegree := left.factorDegree + right.factorDegree
  shortStepDegree := left.shortStepDegree + right.shortStepDegree

/-- A short golden step contributes one to the second degree; a long step
contributes zero. -/
def shortStepIndicator (event : PrimeGoldenStepEvent) : Nat :=
  if Even ((Nat.zeckendorf (event.layer + 1)).getLastD 0) then 0 else 1

/-- Number of short golden steps in a finite event word. -/
def shortStepCount (events : List PrimeGoldenStepEvent) : Nat :=
  (events.map shortStepIndicator).sum

/-- The prime-factor and short-golden-step bidegree of a finite word. -/
def primeGoldenBidegree
    (events : List PrimeGoldenStepEvent) : PrimeGoldenBidegree where
  factorDegree := events.length
  shortStepDegree := shortStepCount events

@[simp]
theorem short_step_count_nil : shortStepCount [] = 0 := by
  rfl

@[simp]
theorem short_step_count_cons
    (event : PrimeGoldenStepEvent) (events : List PrimeGoldenStepEvent) :
    shortStepCount (event :: events) =
      shortStepIndicator event + shortStepCount events := by
  rfl

/-- Short-step degree is additive under chronological concatenation. -/
theorem short_step_count_append
    (earlier later : List PrimeGoldenStepEvent) :
    shortStepCount (earlier ++ later) =
      shortStepCount earlier + shortStepCount later := by
  simp [shortStepCount]

/-- Reversing a word preserves its unsigned short-step count. -/
theorem short_step_count_reverse
    (events : List PrimeGoldenStepEvent) :
    shortStepCount events.reverse = shortStepCount events := by
  simp [shortStepCount]

/-- The bidegree is additive under chronological concatenation. -/
theorem prime_golden_bidegree_append
    (earlier later : List PrimeGoldenStepEvent) :
    primeGoldenBidegree (earlier ++ later) =
      bidegreeAdd (primeGoldenBidegree earlier)
        (primeGoldenBidegree later) := by
  ext <;>
    simp [primeGoldenBidegree, bidegreeAdd, short_step_count_append]

/-- Reversing a word preserves both unsigned degrees. -/
theorem prime_golden_bidegree_reverse
    (events : List PrimeGoldenStepEvent) :
    primeGoldenBidegree events.reverse = primeGoldenBidegree events := by
  ext <;>
    simp [primeGoldenBidegree, short_step_count_reverse]

/-- A step-two chronological signature equipped with its prime-golden
bidegree. -/
@[ext]
structure PrimeGoldenBigradedSignature (A : Type u) where
  chronological : StepTwoSignature A
  bidegree : PrimeGoldenBidegree

/-- The bigraded signature of a finite event word. -/
def bigradedChronologicalSignature
    {A : Type u} [Semiring A]
    (observe : PrimeGoldenStepEvent → A)
    (events : List PrimeGoldenStepEvent) :
    PrimeGoldenBigradedSignature A where
  chronological := chronologicalSignature observe events
  bidegree := primeGoldenBidegree events

/-- Composition multiplies chronological signatures and adds the two degrees. -/
def bigradedCompose
    {A : Type u} [Semiring A]
    (left right : PrimeGoldenBigradedSignature A) :
    PrimeGoldenBigradedSignature A where
  chronological := left.chronological * right.chronological
  bidegree := bidegreeAdd left.bidegree right.bidegree

/-- Chen concatenation and bidegree addition hold in one packaged identity. -/
theorem bigraded_chronological_signature_append
    {A : Type u} [Semiring A]
    (observe : PrimeGoldenStepEvent → A)
    (earlier later : List PrimeGoldenStepEvent) :
    bigradedChronologicalSignature observe (earlier ++ later) =
      bigradedCompose
        (bigradedChronologicalSignature observe earlier)
        (bigradedChronologicalSignature observe later) := by
  apply PrimeGoldenBigradedSignature.ext
  · exact chronological_signature_append observe earlier later
  · exact prime_golden_bidegree_append earlier later

/-- The bigraded antipode reverses chronology and leaves the unsigned degree
labels unchanged. -/
def bigradedAntipode
    {A : Type u} [Ring A]
    (signature : PrimeGoldenBigradedSignature A) :
    PrimeGoldenBigradedSignature A where
  chronological := signatureAntipode signature.chronological
  bidegree := signature.bidegree

/-- Reverse-and-negate realizes the chronological Hopf antipode while
preserving the prime-golden bidegree. -/
theorem bigraded_chronological_time_reversal
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (events : List PrimeGoldenStepEvent) :
    bigradedChronologicalSignature
        (fun event => -observe event) events.reverse =
      bigradedAntipode (bigradedChronologicalSignature observe events) := by
  apply PrimeGoldenBigradedSignature.ext
  · exact chronological_signature_reverse_neg observe events
  · exact prime_golden_bidegree_reverse events

/-- Prime-factor parity character of a bidegree. -/
def factorParityCharacter (degree : PrimeGoldenBidegree) : Int :=
  (-1 : Int) ^ degree.factorDegree

/-- Golden short-step parity character of a bidegree. -/
def goldenStepParityCharacter (degree : PrimeGoldenBidegree) : Int :=
  (-1 : Int) ^ degree.shortStepDegree

/-- Product character on the two parity coordinates. -/
def jointParityCharacter (degree : PrimeGoldenBidegree) : Int :=
  factorParityCharacter degree * goldenStepParityCharacter degree

/-- Each parity character is multiplicative under bidegree addition. -/
theorem bidegree_parity_characters_add
    (left right : PrimeGoldenBidegree) :
    factorParityCharacter (bidegreeAdd left right) =
        factorParityCharacter left * factorParityCharacter right ∧
      goldenStepParityCharacter (bidegreeAdd left right) =
        goldenStepParityCharacter left * goldenStepParityCharacter right ∧
      jointParityCharacter (bidegreeAdd left right) =
        jointParityCharacter left * jointParityCharacter right := by
  constructor
  · simp [factorParityCharacter, bidegreeAdd, pow_add]
  constructor
  · simp [goldenStepParityCharacter, bidegreeAdd, pow_add]
  · simp [jointParityCharacter, factorParityCharacter,
      goldenStepParityCharacter, bidegreeAdd, pow_add]
    ring

/-- The first degree is exactly the total prime-factor count of the represented
integer, with multiplicity. -/
theorem factor_degree_eq_card_factors
    (events : List PrimeGoldenStepEvent) :
    ArithmeticFunction.cardFactors (primeWordProduct events) =
      (primeGoldenBidegree events).factorDegree := by
  induction events with
  | nil =>
      simp [primeWordProduct, primeGoldenBidegree]
  | cons event events inductionHypothesis =>
      have hTail :
          ArithmeticFunction.cardFactors (primeWordProduct events) =
            events.length := by
        simpa [primeGoldenBidegree] using inductionHypothesis
      change
        ArithmeticFunction.cardFactors
            ((event.prime : Nat) * primeWordProduct events) =
          events.length + 1
      rw [ArithmeticFunction.cardFactors_mul
          event.prime.property.ne_zero
          (prime_word_product_ne_zero events),
        ArithmeticFunction.cardFactors_apply_prime event.prime.property,
        hTail]
      omega

/-- Liouville is precisely the parity character of the prime-factor degree. -/
theorem factor_parity_character_eq_liouville
    (events : List PrimeGoldenStepEvent) :
    factorParityCharacter (primeGoldenBidegree events) =
      ArithmeticFunction.liouville (primeWordProduct events) := by
  simpa [factorParityCharacter, primeGoldenBidegree] using
    (liouville_prime_word_product events).symm

/-- Local long/short sign attached to one Zeckendorf-selected step. -/
def goldenStepParityLetter (event : PrimeGoldenStepEvent) : Int :=
  if Even ((Nat.zeckendorf (event.layer + 1)).getLastD 0) then 1 else -1

/-- A local step sign is `-1` to the power of its short-step indicator. -/
theorem golden_step_parity_letter_eq_pow
    (event : PrimeGoldenStepEvent) :
    goldenStepParityLetter event =
      (-1 : Int) ^ shortStepIndicator event := by
  unfold goldenStepParityLetter shortStepIndicator
  by_cases hEven : Even ((Nat.zeckendorf (event.layer + 1)).getLastD 0)
  · simp [hEven]
  · simp [hEven]

/-- The second parity character is the product of all local golden step signs. -/
theorem golden_step_parity_character_eq_letter_product
    (events : List PrimeGoldenStepEvent) :
    goldenStepParityCharacter (primeGoldenBidegree events) =
      (events.map goldenStepParityLetter).prod := by
  induction events with
  | nil =>
      simp [goldenStepParityCharacter, primeGoldenBidegree, shortStepCount]
  | cons event events inductionHypothesis =>
      calc
        goldenStepParityCharacter
            (primeGoldenBidegree (event :: events)) =
          (-1 : Int) ^ shortStepIndicator event *
            goldenStepParityCharacter (primeGoldenBidegree events) := by
              simp [goldenStepParityCharacter, primeGoldenBidegree,
                shortStepCount, pow_add]
        _ = (-1 : Int) ^ shortStepIndicator event *
            (events.map goldenStepParityLetter).prod := by
              rw [inductionHypothesis]
        _ = goldenStepParityLetter event *
            (events.map goldenStepParityLetter).prod := by
              rw [golden_step_parity_letter_eq_pow]
        _ = ((event :: events).map goldenStepParityLetter).prod := by
              rfl

/-- The frequency of one event is the long golden weight minus its short-step
indicator, all scaled by the logarithm of the prime channel. -/
theorem step_frequency_eq_bidegree_letter
    (event : PrimeGoldenStepEvent) :
    stepFrequency event =
      (Real.goldenRatio ^ 2 - (shortStepIndicator event : Real)) *
        Real.log ((event.prime : Nat) : Real) := by
  rw [step_frequency_zeckendorf_parity]
  unfold shortStepIndicator
  by_cases hEven : Even ((Nat.zeckendorf (event.layer + 1)).getLastD 0)
  · simp [hEven]
  · simp [hEven, Real.goldenRatio_sq]

/-- All events in the word use one fixed prime channel. -/
def IsSinglePrimeWord
    (prime : Nat.Primes) (events : List PrimeGoldenStepEvent) : Prop :=
  ∀ event ∈ events, event.prime = prime

/-- Frequency represented by one bidegree inside a fixed prime channel. -/
def bidegreeFrequency
    (prime : Nat.Primes) (degree : PrimeGoldenBidegree) : Real :=
  ((degree.factorDegree : Real) * Real.goldenRatio ^ 2 -
      (degree.shortStepDegree : Real)) *
    Real.log ((prime : Nat) : Real)

private theorem sum_step_weights_eq_bidegree
    (events : List PrimeGoldenStepEvent) (scale : Real) :
    (events.map fun event =>
        (Real.goldenRatio ^ 2 - (shortStepIndicator event : Real)) *
          scale).sum =
      ((events.length : Real) * Real.goldenRatio ^ 2 -
          (shortStepCount events : Real)) * scale := by
  induction events with
  | nil =>
      simp [shortStepCount]
  | cons event events inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        short_step_count_cons]
      rw [inductionHypothesis]
      push_cast
      ring

/-- In one prime channel, the complete frequency sum is determined exactly by
the prime-factor and short-step bidegree. -/
theorem total_step_frequency_eq_bidegree_of_single_prime
    (prime : Nat.Primes) (events : List PrimeGoldenStepEvent)
    (hSingle : IsSinglePrimeWord prime events) :
    totalStepFrequency events =
      bidegreeFrequency prime (primeGoldenBidegree events) := by
  calc
    totalStepFrequency events =
        (events.map fun event =>
          (Real.goldenRatio ^ 2 - (shortStepIndicator event : Real)) *
            Real.log ((event.prime : Nat) : Real)).sum := by
      unfold totalStepFrequency
      apply congrArg List.sum
      apply List.map_congr_left
      intro event hmem
      exact step_frequency_eq_bidegree_letter event
    _ =
        (events.map fun event =>
          (Real.goldenRatio ^ 2 - (shortStepIndicator event : Real)) *
            Real.log ((prime : Nat) : Real)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro event hmem
      rw [hSingle event hmem]
    _ = bidegreeFrequency prime (primeGoldenBidegree events) := by
      rw [sum_step_weights_eq_bidegree]
      rfl

/-- Scalar phase determined by a bidegree in one prime channel. -/
def bidegreePhase
    (time : Real) (prime : Nat.Primes)
    (degree : PrimeGoldenBidegree) : Complex :=
  Complex.exp
    (((time * bidegreeFrequency prime degree : Real) : Complex) * Complex.I)

/-- A scalar event-word endpoint collapses to the exponential of the summed
frequency. -/
theorem scalar_step_endpoint_eq_total_frequency
    (time : Real) (events : List PrimeGoldenStepEvent) :
    scalarStepEndpoint time events =
      Complex.exp
        (((time * totalStepFrequency events : Real) : Complex) * Complex.I) := by
  induction events with
  | nil =>
      simp [scalarStepEndpoint, totalStepFrequency, stepPhase]
  | cons event events inductionHypothesis =>
      change
        stepPhase time event * scalarStepEndpoint time events =
          Complex.exp
            (((time *
              (stepFrequency event + totalStepFrequency events) : Real) : Complex) *
              Complex.I)
      rw [inductionHypothesis]
      unfold stepPhase
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- In a fixed prime channel, the terminal scalar phase factors through the
prime-golden bidegree. -/
theorem scalar_step_endpoint_eq_bidegree_phase_of_single_prime
    (time : Real) (prime : Nat.Primes)
    (events : List PrimeGoldenStepEvent)
    (hSingle : IsSinglePrimeWord prime events) :
    scalarStepEndpoint time events =
      bidegreePhase time prime (primeGoldenBidegree events) := by
  rw [scalar_step_endpoint_eq_total_frequency,
    total_step_frequency_eq_bidegree_of_single_prime prime events hSingle]
  rfl

/-- Headline law: reverse-and-negate takes the Hopf antipode, preserves the
bidegree and both parity ledgers, and the fixed-prime scalar endpoint factors
through that bidegree. -/
theorem prime_golden_bigraded_time_reversal_laws
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (time : Real) (prime : Nat.Primes)
    (events : List PrimeGoldenStepEvent)
    (hSingle : IsSinglePrimeWord prime events) :
    bigradedChronologicalSignature
        (fun event => -observe event) events.reverse =
        bigradedAntipode (bigradedChronologicalSignature observe events) ∧
      factorParityCharacter (primeGoldenBidegree events) =
        ArithmeticFunction.liouville (primeWordProduct events) ∧
      goldenStepParityCharacter (primeGoldenBidegree events) =
        (events.map goldenStepParityLetter).prod ∧
      scalarStepEndpoint time events =
        bidegreePhase time prime (primeGoldenBidegree events) ∧
      doubledMagnusDegreeTwo
          (chronologicalSignature (fun event => -observe event) events.reverse) =
        -doubledMagnusDegreeTwo (chronologicalSignature observe events) := by
  exact
    ⟨bigraded_chronological_time_reversal observe events,
      factor_parity_character_eq_liouville events,
      golden_step_parity_character_eq_letter_product events,
      scalar_step_endpoint_eq_bidegree_phase_of_single_prime
        time prime events hSingle,
      doubled_magnus_prime_step_time_reversal observe events⟩

#print axioms prime_golden_bidegree_append
#print axioms bigraded_chronological_signature_append
#print axioms bigraded_chronological_time_reversal
#print axioms factor_degree_eq_card_factors
#print axioms factor_parity_character_eq_liouville
#print axioms golden_step_parity_character_eq_letter_product
#print axioms step_frequency_eq_bidegree_letter
#print axioms total_step_frequency_eq_bidegree_of_single_prime
#print axioms scalar_step_endpoint_eq_bidegree_phase_of_single_prime
#print axioms prime_golden_bigraded_time_reversal_laws

end

end D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature
