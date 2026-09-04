/- GID: D5/S3/Observer/Chronology/PrimeGoldenChronologyFiberSeparation
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Scalar prime-golden observation is constant on a fixed bidegree fiber, while a noncommutative second-Magnus readout can separate swapped event orders inside that fiber. -/

import D5.S3.Observer.Chronology.PrimeGoldenBidegreePhaseSeparation
import D5.S3.Observer.Chronology.StepTwoChronologicalSignature
import Mathlib.Tactic

/-!
# Prime-golden chronology fiber separation

The fixed-prime scalar observer factors through the prime-golden bidegree. All
words in one fixed bidegree fiber therefore have the same complete scalar phase
trajectory. The fiber can still contain different chronological words.

For a two-event word and its reversal, the bidegree and complete scalar phase
trajectory agree. Their second-Magnus coordinates are the two oriented
commutators. Whenever these commutators differ, the noncommutative readout
separates the two histories inside the same scalar observation fiber.

This is a finite step-two separation theorem. It does not claim that every pair
of words with the same bidegree is separated at degree two, construct a
step-three signature, or identify the observer with physical time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeGoldenChronologyFiberSeparation

open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
open D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature
open D5.S3.Observer.Chronology.PrimeGoldenBidegreeFrequencyRigidity
open D5.S3.Observer.Chronology.PrimeGoldenBidegreePhaseSeparation

noncomputable section

universe u

/-- Membership in the scalar fiber determined by one prime channel and one
prime-golden bidegree. -/
def InPrimeBidegreeFiber
    (prime : Nat.Primes) (degree : PrimeGoldenBidegree)
    (events : List PrimeGoldenStepEvent) : Prop :=
  IsSinglePrimeWord prime events ∧ primeGoldenBidegree events = degree

/-- Two event words have the same complete scalar Euler trajectory. -/
def SameScalarTrajectory
    (left right : List PrimeGoldenStepEvent) : Prop :=
  ∀ time : Real,
    scalarStepEndpoint time left = scalarStepEndpoint time right

/-- Scalar phase is constant on every fixed-prime bidegree fiber. -/
theorem prime_bidegree_fiber_scalar_constant
    (prime : Nat.Primes) (degree : PrimeGoldenBidegree)
    {left right : List PrimeGoldenStepEvent}
    (hLeft : InPrimeBidegreeFiber prime degree left)
    (hRight : InPrimeBidegreeFiber prime degree right) :
    SameScalarTrajectory left right := by
  intro time
  rw [scalar_step_endpoint_eq_bidegree_phase_of_single_prime
      time prime left hLeft.1,
    scalar_step_endpoint_eq_bidegree_phase_of_single_prime
      time prime right hRight.1,
    hLeft.2, hRight.2]

/-- A two-event word and its reversal have the same prime-golden bidegree. -/
theorem two_event_swapped_bidegree_eq
    (first second : PrimeGoldenStepEvent) :
    primeGoldenBidegree [first, second] =
      primeGoldenBidegree [second, first] := by
  simpa using prime_golden_bidegree_reverse [first, second]

/-- A two-event word and its reversal have the same complete scalar phase
trajectory. -/
theorem two_event_swapped_scalar_trajectory
    (first second : PrimeGoldenStepEvent) :
    SameScalarTrajectory [first, second] [second, first] := by
  intro time
  simpa using scalar_step_endpoint_reverse time [first, second]

/-- If both events use one prime channel, the word and its reversal lie in the
same fixed-prime bidegree fiber. -/
theorem swapped_two_event_words_in_same_prime_bidegree_fiber
    (prime : Nat.Primes) (first second : PrimeGoldenStepEvent)
    (hFirst : first.prime = prime)
    (hSecond : second.prime = prime) :
    InPrimeBidegreeFiber prime
        (primeGoldenBidegree [first, second]) [first, second] ∧
      InPrimeBidegreeFiber prime
        (primeGoldenBidegree [first, second]) [second, first] := by
  constructor
  · constructor
    · intro event hmem
      simp only [List.mem_cons, List.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact hFirst
      · exact hSecond
    · rfl
  · constructor
    · intro event hmem
      simp only [List.mem_cons, List.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact hSecond
      · exact hFirst
    · exact (two_event_swapped_bidegree_eq first second).symm

/-- The second-Magnus readouts of a two-event word and its reversal are the two
oriented commutators. -/
theorem two_event_swapped_magnus_coordinates
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (first second : PrimeGoldenStepEvent) :
    doubledMagnusDegreeTwo
        (chronologicalSignature observe [first, second]) =
        commutator (observe first) (observe second) ∧
      doubledMagnusDegreeTwo
        (chronologicalSignature observe [second, first]) =
        commutator (observe second) (observe first) := by
  exact
    ⟨doubled_magnus_two_events_eq_commutator observe first second,
      doubled_magnus_two_events_eq_commutator observe second first⟩

/-- An asymmetric commutator separates the two reversed histories at Magnus
degree two. -/
theorem two_event_swapped_magnus_separated
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (first second : PrimeGoldenStepEvent)
    (hOriented :
      commutator (observe first) (observe second) ≠
        commutator (observe second) (observe first)) :
    doubledMagnusDegreeTwo
        (chronologicalSignature observe [first, second]) ≠
      doubledMagnusDegreeTwo
        (chronologicalSignature observe [second, first]) := by
  rw [doubled_magnus_two_events_eq_commutator,
    doubled_magnus_two_events_eq_commutator]
  exact hOriented

/-- Headline separation theorem. Swapped two-event histories occupy the same
bidegree and scalar phase fiber, while a genuinely oriented noncommutative
observer distinguishes them. -/
theorem prime_golden_chronology_fiber_separation
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (first second : PrimeGoldenStepEvent)
    (hOriented :
      commutator (observe first) (observe second) ≠
        commutator (observe second) (observe first)) :
    primeGoldenBidegree [first, second] =
        primeGoldenBidegree [second, first] ∧
      SameScalarTrajectory [first, second] [second, first] ∧
      doubledMagnusDegreeTwo
          (chronologicalSignature observe [first, second]) ≠
        doubledMagnusDegreeTwo
          (chronologicalSignature observe [second, first]) := by
  exact
    ⟨two_event_swapped_bidegree_eq first second,
      two_event_swapped_scalar_trajectory first second,
      two_event_swapped_magnus_separated
        observe first second hOriented⟩

#print axioms prime_bidegree_fiber_scalar_constant
#print axioms two_event_swapped_bidegree_eq
#print axioms two_event_swapped_scalar_trajectory
#print axioms swapped_two_event_words_in_same_prime_bidegree_fiber
#print axioms two_event_swapped_magnus_coordinates
#print axioms two_event_swapped_magnus_separated
#print axioms prime_golden_chronology_fiber_separation

end

end D5.S3.Observer.Chronology.PrimeGoldenChronologyFiberSeparation
