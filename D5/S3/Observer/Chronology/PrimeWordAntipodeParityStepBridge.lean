/- GID: D5/S3/Observer/Chronology/PrimeWordAntipodeParityStepBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/Mathlib.NumberTheory.ArithmeticFunction.Liouville, mathlib/Mathlib.NumberTheory.ArithmeticFunction.Moebius]
   digest: Prime-word time reversal retains chronology in the Magnus lift, leaves Liouville factor parity after commutative readout, and preserves the reversed golden step total. -/

import D5.S3.Analytic.GoldenEulerBetaZeckendorf
import D5.S3.Observer.Chronology.ChronologicalSignatureHopf
import D5.S3.Observer.GoldenPrimeCircle.GoldenEulerStepPhaseLaw
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Prime-word antipode, factor parity, and golden step reversal

A chronological prime-step event carries two independent discrete coordinates:
a prime channel and a golden layer. The prime word can be read in three ways.

* The step-two chronological signature keeps the ordered word. Its antipode
  reverses the word and negates every observed increment, and its logarithmic
  Magnus coordinates change sign.
* A commutative integer readout forgets the reversal. Negating every prime
  letter leaves only the degree sign `(-1)^word.length`; for the product of the
  prime letters this is exactly the Liouville function.
* The golden step readout is selected by the least Zeckendorf-index parity.
  Reversing the event list preserves the total frequency and the terminal
  scalar phase, while negating the external time parameter gives the inverse
  unitary evolution.

The Möbius function is recorded as a second projection: it agrees with the
Liouville sign on squarefree prime products and vanishes when squarefreeness
fails. Thus Möbius is factor parity together with a collision filter, whereas
Liouville keeps multiplicity parity.

The factor-count parity and the Zeckendorf least-index parity are not
identified. They are separate `Z/2` coordinates on the same event stream.
This finite bridge makes no infinite-signature, analytic-continuation,
zeta-zero, physical arrow-of-time, or Riemann-hypothesis claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge

open D5.S3.Analytic.GoldenEulerBetaZeckendorf
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepTwoChronologicalLogarithm
open D5.S3.Observer.Chronology.ChronologicalSignatureHopf
open D5.S3.Observer.GoldenPrimeCircle.GoldenEulerStepPhaseLaw

noncomputable section

universe u

/-- One event in the joint prime-channel and golden-layer chronology. -/
@[ext]
structure PrimeGoldenStepEvent where
  prime : Nat.Primes
  layer : Nat

/-- The ordinary integer represented by the listed prime events, with
multiplicity retained. -/
def primeWordProduct (events : List PrimeGoldenStepEvent) : Nat :=
  (events.map fun event => (event.prime : Nat)).prod

/-- The commutative integer-algebra readout of a prime word. -/
def commutativePrimeWordReadout
    (events : List PrimeGoldenStepEvent) : Int :=
  (events.map fun event => ((event.prime : Nat) : Int)).prod

/-- The same commutative readout after the word antipode: reverse the list and
negate every primitive prime letter. -/
def antipodePrimeWordReadout
    (events : List PrimeGoldenStepEvent) : Int :=
  (events.reverse.map fun event => -((event.prime : Nat) : Int)).prod

/-- The frequency increment carried by one joint prime-layer event. -/
def stepFrequency (event : PrimeGoldenStepEvent) : Real :=
  primeStepFrequency event.prime event.layer

/-- The positive-sign Euler phase associated with one joint prime-layer
frequency increment. -/
def stepPhase (time : Real) (event : PrimeGoldenStepEvent) : Complex :=
  Complex.exp
    (((time * stepFrequency event : Real) : Complex) * Complex.I)

/-- The additive scalar frequency readout of a finite event word. -/
def totalStepFrequency (events : List PrimeGoldenStepEvent) : Real :=
  (events.map stepFrequency).sum

/-- The commutative terminal phase of a finite event word. -/
def scalarStepEndpoint
    (time : Real) (events : List PrimeGoldenStepEvent) : Complex :=
  (events.map fun event => stepPhase time event).prod

private theorem reverse_negated_product
    {Event : Type*} (weight : Event → Int) (events : List Event) :
    (events.reverse.map fun event => -weight event).prod =
      (-1 : Int) ^ events.length * (events.map weight).prod := by
  induction events with
  | nil => simp
  | cons event events inductionHypothesis =>
      rw [List.reverse_cons, List.map_append, List.prod_append]
      simp only [List.map_singleton, List.prod_singleton,
        List.length_cons, List.map_cons, List.prod_cons]
      rw [inductionHypothesis, pow_succ]
      ring

/-- A product of prime events is never zero. -/
theorem prime_word_product_ne_zero
    (events : List PrimeGoldenStepEvent) :
    primeWordProduct events ≠ 0 := by
  induction events with
  | nil => simp [primeWordProduct]
  | cons event events inductionHypothesis =>
      change (event.prime : Nat) * primeWordProduct events ≠ 0
      exact mul_ne_zero event.prime.property.ne_zero inductionHypothesis

/-- The integer readout is the integer cast of the natural prime product. -/
theorem commutative_prime_word_readout_eq_nat_cast
    (events : List PrimeGoldenStepEvent) :
    commutativePrimeWordReadout events = (primeWordProduct events : Int) := by
  induction events with
  | nil => simp [commutativePrimeWordReadout, primeWordProduct]
  | cons event events inductionHypothesis =>
      change
        ((event.prime : Nat) : Int) * commutativePrimeWordReadout events =
          (((event.prime : Nat) * primeWordProduct events : Nat) : Int)
      rw [inductionHypothesis, Nat.cast_mul]

/-- The antipode's commutative prime readout factors into the word-length sign
and the unsigned prime readout. Word reversal itself disappears because the
target multiplication is commutative. -/
theorem antipode_prime_word_readout_factorization
    (events : List PrimeGoldenStepEvent) :
    antipodePrimeWordReadout events =
      (-1 : Int) ^ events.length * commutativePrimeWordReadout events := by
  simpa [antipodePrimeWordReadout, commutativePrimeWordReadout] using
    reverse_negated_product
      (fun event : PrimeGoldenStepEvent => ((event.prime : Nat) : Int))
      events

/-- Liouville parity of the represented integer is exactly the parity of the
number of prime events, counting multiplicity. -/
theorem liouville_prime_word_product
    (events : List PrimeGoldenStepEvent) :
    ArithmeticFunction.liouville (primeWordProduct events) =
      (-1 : Int) ^ events.length := by
  induction events with
  | nil =>
      simpa [primeWordProduct] using ArithmeticFunction.liouville_apply_one
  | cons event events inductionHypothesis =>
      change
        ArithmeticFunction.liouville
            ((event.prime : Nat) * primeWordProduct events) =
          (-1 : Int) ^ (events.length + 1)
      rw [ArithmeticFunction.liouville_apply_mul]
      have primeValue :
          ArithmeticFunction.liouville (event.prime : Nat) = -1 := by
        rw [ArithmeticFunction.liouville_apply event.prime.property.ne_zero,
          ArithmeticFunction.cardFactors_apply_prime event.prime.property]
        norm_num
      rw [primeValue, inductionHypothesis, pow_succ]
      ring

/-- Liouville is the scalar parity shadow of prime-word time reversal. The
ordered reversal is absent from the commutative target, while its degree sign
remains. -/
theorem antipode_prime_word_readout_eq_liouville
    (events : List PrimeGoldenStepEvent) :
    antipodePrimeWordReadout events =
      ArithmeticFunction.liouville (primeWordProduct events) *
        commutativePrimeWordReadout events := by
  rw [antipode_prime_word_readout_factorization,
    liouville_prime_word_product]

/-- On a squarefree prime product, Möbius and Liouville carry the same parity
sign. -/
theorem moebius_eq_liouville_of_squarefree_prime_word
    (events : List PrimeGoldenStepEvent)
    (hSquarefree : Squarefree (primeWordProduct events)) :
    ArithmeticFunction.moebius (primeWordProduct events) =
      ArithmeticFunction.liouville (primeWordProduct events) := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hSquarefree,
    ArithmeticFunction.liouville_apply (prime_word_product_ne_zero events)]

/-- Failure of squarefreeness sends the Möbius channel to zero. This is the
collision-filter component absent from Liouville parity. -/
theorem moebius_eq_zero_of_nonsquarefree_prime_word
    (events : List PrimeGoldenStepEvent)
    (hNotSquarefree : ¬Squarefree (primeWordProduct events)) :
    ArithmeticFunction.moebius (primeWordProduct events) = 0 := by
  exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hNotSquarefree

/-- The parity of the least occupied Zeckendorf index selects the long or
short prime-local step. This parity is independent of prime-factor count. -/
theorem step_frequency_zeckendorf_parity
    (event : PrimeGoldenStepEvent) :
    stepFrequency event =
      if Even ((Nat.zeckendorf (event.layer + 1)).getLastD 0) then
        Real.goldenRatio ^ 2 *
          Real.log ((event.prime : Nat) : Real)
      else
        Real.goldenRatio *
          Real.log ((event.prime : Nat) : Real) := by
  have gapLaw :=
    (golden_euler_beta_zeckendorf).2.2 event.layer
  unfold stepFrequency
  unfold primeStepFrequency
  rw [D5.S3.Analytic.EulerGerm.PrimeZeckendorfFrequencyBridge.prime_layer_frequency_gap,
    gapLaw]
  by_cases hEven : Even ((Nat.zeckendorf (event.layer + 1)).getLastD 0)
  · simp [hEven]
  · simp [hEven]

/-- The same least-index parity selects the corresponding Euler phase letter. -/
theorem step_phase_zeckendorf_parity
    (time : Real) (event : PrimeGoldenStepEvent) :
    stepPhase time event =
      if Even ((Nat.zeckendorf (event.layer + 1)).getLastD 0) then
        Complex.exp
          (((time *
            (Real.goldenRatio ^ 2 *
              Real.log ((event.prime : Nat) : Real)) : Real) : Complex) *
            Complex.I)
      else
        Complex.exp
          (((time *
            (Real.goldenRatio *
              Real.log ((event.prime : Nat) : Real)) : Real) : Complex) *
            Complex.I) := by
  unfold stepPhase
  rw [step_frequency_zeckendorf_parity]
  by_cases hEven : Even ((Nat.zeckendorf (event.layer + 1)).getLastD 0)
  · simp [hEven]
  · simp [hEven]

/-- Reversing the event word preserves its additive golden frequency total. -/
theorem total_step_frequency_reverse
    (events : List PrimeGoldenStepEvent) :
    totalStepFrequency events.reverse = totalStepFrequency events := by
  simp [totalStepFrequency]

/-- Reversing the event word preserves its terminal scalar Euler phase because
complex multiplication is commutative. -/
theorem scalar_step_endpoint_reverse
    (time : Real) (events : List PrimeGoldenStepEvent) :
    scalarStepEndpoint time events.reverse = scalarStepEndpoint time events := by
  simp [scalarStepEndpoint]

/-- Negating the external time parameter inverts one unitary step phase. -/
theorem step_phase_time_reversal_mul
    (time : Real) (event : PrimeGoldenStepEvent) :
    stepPhase (-time) event * stepPhase time event = 1 := by
  unfold stepPhase
  rw [← Complex.exp_add]
  have exponentCancellation :
      (((-time * stepFrequency event : Real) : Complex) * Complex.I) +
          (((time * stepFrequency event : Real) : Complex) * Complex.I) = 0 := by
    push_cast
    ring
  rw [exponentCancellation, Complex.exp_zero]

/-- Negating the external time parameter inverts the complete scalar endpoint. -/
theorem scalar_step_endpoint_time_reversal_mul
    (time : Real) (events : List PrimeGoldenStepEvent) :
    scalarStepEndpoint (-time) events * scalarStepEndpoint time events = 1 := by
  induction events with
  | nil => simp [scalarStepEndpoint]
  | cons event events inductionHypothesis =>
      change
        (stepPhase (-time) event * scalarStepEndpoint (-time) events) *
            (stepPhase time event * scalarStepEndpoint time events) = 1
      calc
        (stepPhase (-time) event * scalarStepEndpoint (-time) events) *
            (stepPhase time event * scalarStepEndpoint time events) =
          (stepPhase (-time) event * stepPhase time event) *
            (scalarStepEndpoint (-time) events *
              scalarStepEndpoint time events) := by ring
        _ = 1 := by
          rw [step_phase_time_reversal_mul, inductionHypothesis]
          norm_num

/-- Specialization of the frozen Hopf reversal law to joint prime-step event
words. -/
theorem chronological_prime_step_time_reversal
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (events : List PrimeGoldenStepEvent) :
    chronologicalSignature (fun event => -observe event) events.reverse =
      signatureAntipode (chronologicalSignature observe events) := by
  exact chronological_signature_reverse_neg observe events

/-- Every step-two Magnus coordinate changes sign under chronological time
reversal. This primitive-coordinate sign is present for every word length;
it is distinct from the even/odd scalar factor sign. -/
theorem doubled_magnus_prime_step_time_reversal
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (events : List PrimeGoldenStepEvent) :
    doubledMagnusDegreeTwo
        (chronologicalSignature (fun event => -observe event) events.reverse) =
      -doubledMagnusDegreeTwo (chronologicalSignature observe events) := by
  have logarithmLaw := chronological_log_reverse_neg observe events
  have degreeTwoLaw := congrArg
    (fun coordinate : StepTwoLogarithm A => coordinate.doubledLieDegreeTwo)
    logarithmLaw
  simpa [chronologicalLog, StepTwoLogarithm.inverse] using degreeTwoLaw

/-- Headline trichotomy for one prime-step event stream. Commutative prime
readout retains only Liouville degree parity, scalar golden readout forgets
word reversal, and the noncommutative Magnus lift retains oriented chronology. -/
theorem prime_word_time_reversal_readout_trichotomy
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (time : Real) (events : List PrimeGoldenStepEvent) :
    antipodePrimeWordReadout events =
        ArithmeticFunction.liouville (primeWordProduct events) *
          commutativePrimeWordReadout events ∧
      totalStepFrequency events.reverse = totalStepFrequency events ∧
      scalarStepEndpoint time events.reverse = scalarStepEndpoint time events ∧
      doubledMagnusDegreeTwo
          (chronologicalSignature (fun event => -observe event) events.reverse) =
        -doubledMagnusDegreeTwo (chronologicalSignature observe events) := by
  exact
    ⟨antipode_prime_word_readout_eq_liouville events,
      total_step_frequency_reverse events,
      scalar_step_endpoint_reverse time events,
      doubled_magnus_prime_step_time_reversal observe events⟩

#print axioms antipode_prime_word_readout_eq_liouville
#print axioms moebius_eq_liouville_of_squarefree_prime_word
#print axioms moebius_eq_zero_of_nonsquarefree_prime_word
#print axioms step_frequency_zeckendorf_parity
#print axioms scalar_step_endpoint_time_reversal_mul
#print axioms chronological_prime_step_time_reversal
#print axioms doubled_magnus_prime_step_time_reversal
#print axioms prime_word_time_reversal_readout_trichotomy

end

end D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
