/- GID: D5/S3/Observer/Chronology/StepTwoChronologicalSignature
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/StepTwoChronologicalSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Step-two signatures obey Chen concatenation and the degree-two BCH law. -/

import D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity
import Mathlib.Tactic

/-!
# Step-two chronological signature

A single event with algebra value `x` is represented by the degree-one value
`x` and the doubled degree-two value `x * x`. Composition of two truncated
signatures adds degree one and adds the chronological cross term
`2 * left.degreeOne * right.degreeOne` at degree two. This operation is a
monoid, and the signature of a concatenated event word is the product of the
signatures of its two chronological pieces.

Subtracting the square of degree one from doubled degree two gives the doubled
degree-two logarithmic coordinate. It obeys the step-two
Baker-Campbell-Hausdorff law: concatenation adds the two logarithmic
coordinates and the commutator of the two degree-one coordinates. For a word
of exactly two events, this coordinate is exactly their commutator, and
reversing the two events negates it.

This file freezes the algebraic step-two truncation. It does not construct the
full tensor or shuffle Hopf algebra, define an infinite signature, prove
analytic convergence, identify primitive elements in a completed Hopf
algebra, integrate a rough path, construct a continuous Magnus series, or
assert that operational chronology supplies a physical arrow of time.
-/

/- Library-search audit trail (2026-09-01):
   * `TimeOrderedPrimeMemoryCocycle` owns one concrete affine chronological
     word action and its twisted append law, but it does not define a reusable
     step-two signature monoid or logarithmic BCH coordinate.
   * `SecondMagnusSwapCurvature` owns a scalar Fourier slot alternant and its
     finite energy, but it does not construct the generic chronological
     signature whose degree-two logarithm is a commutator.
   * `ProjectionCommutatorIdentity` owns the repository-wide ring commutator
     convention and is reused below.
   * Pinned Mathlib contains tensor algebras, free Lie algebras, Hopf algebras,
     primitive elements, and convolution. The present finite truncation is
     intentionally proved from ring laws before those infinite algebraic
     owners are connected in later nodes.
   * Repository search found no existing owner of the step-two signature
     composition law, its exact Chen append identity, and its degree-two BCH
     formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.StepTwoChronologicalSignature

open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

universe u v

/-- Degree one together with twice degree two of a chronological signature.
The doubled convention avoids division by two and remains valid over every
semiring. -/
@[ext]
structure StepTwoSignature (A : Type u) where
  degreeOne : A
  doubledDegreeTwo : A

namespace StepTwoSignature

variable {A : Type u}

/-- Composition of two step-two signatures. Every event represented by the
left input occurs before every event represented by the right input. -/
def compose [Semiring A]
    (left right : StepTwoSignature A) : StepTwoSignature A where
  degreeOne := left.degreeOne + right.degreeOne
  doubledDegreeTwo :=
    left.doubledDegreeTwo +
      2 * (left.degreeOne * right.degreeOne) +
      right.doubledDegreeTwo

/-- The empty chronological signature. -/
def identity [Zero A] : StepTwoSignature A where
  degreeOne := 0
  doubledDegreeTwo := 0

/-- Step-two chronological composition is associative and has the empty
signature as its unit. -/
instance [Semiring A] : Monoid (StepTwoSignature A) where
  one := identity
  mul := compose
  one_mul signature := by
    change compose identity signature = signature
    ext <;> simp [compose, identity]
  mul_one signature := by
    change compose signature identity = signature
    ext <;> simp [compose, identity]
  mul_assoc left middle right := by
    change compose (compose left middle) right =
      compose left (compose middle right)
    ext <;> simp [compose, mul_add, add_mul, mul_assoc] <;> abel

@[simp]
theorem degreeOne_one [Semiring A] :
    (1 : StepTwoSignature A).degreeOne = 0 := by
  rfl

@[simp]
theorem doubledDegreeTwo_one [Semiring A] :
    (1 : StepTwoSignature A).doubledDegreeTwo = 0 := by
  rfl

@[simp]
theorem degreeOne_mul [Semiring A]
    (left right : StepTwoSignature A) :
    (left * right).degreeOne = left.degreeOne + right.degreeOne := by
  rfl

@[simp]
theorem doubledDegreeTwo_mul [Semiring A]
    (left right : StepTwoSignature A) :
    (left * right).doubledDegreeTwo =
      left.doubledDegreeTwo +
        2 * (left.degreeOne * right.degreeOne) +
        right.doubledDegreeTwo := by
  rfl

end StepTwoSignature

/-- The step-two signature of one event value. The doubled degree-two
coordinate is the square contributed by its own truncated exponential. -/
def eventSignature {A : Type u} [Semiring A]
    (value : A) : StepTwoSignature A where
  degreeOne := value
  doubledDegreeTwo := value * value

/-- The step-two signature of an event list read from left to right. -/
def chronologicalSignature
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A) : List Event → StepTwoSignature A
  | [] => 1
  | event :: events =>
      eventSignature (observe event) *
        chronologicalSignature observe events

@[simp]
theorem chronological_signature_nil
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A) :
    chronologicalSignature observe [] = 1 := by
  rfl

@[simp]
theorem chronological_signature_cons
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A) (event : Event) (events : List Event) :
    chronologicalSignature observe (event :: events) =
      eventSignature (observe event) *
        chronologicalSignature observe events := by
  rfl

/-- Chen's concatenation identity at step two: the signature of two
chronological words joined in order is their signature product. -/
theorem chronological_signature_append
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A)
    (earlierWord laterWord : List Event) :
    chronologicalSignature observe (earlierWord ++ laterWord) =
      chronologicalSignature observe earlierWord *
        chronologicalSignature observe laterWord := by
  induction earlierWord with
  | nil =>
      simp [chronologicalSignature]
  | cons event earlierWord ih =>
      simp [chronologicalSignature, ih, mul_assoc]

/-- Degree one of the chronological signature is the ordinary sum of all event
values. It therefore forgets event order. -/
theorem chronological_signature_degree_one
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A) (events : List Event) :
    (chronologicalSignature observe events).degreeOne =
      (events.map observe).sum := by
  induction events with
  | nil =>
      simp [chronologicalSignature]
  | cons event events ih =>
      simp [chronologicalSignature, eventSignature, ih]

/-- Twice the degree-two logarithmic coordinate of a step-two signature. -/
def doubledMagnusDegreeTwo
    {A : Type u} [Ring A] (signature : StepTwoSignature A) : A :=
  signature.doubledDegreeTwo -
    signature.degreeOne * signature.degreeOne

@[simp]
theorem doubled_magnus_degree_two_event
    {A : Type u} [Ring A] (value : A) :
    doubledMagnusDegreeTwo (eventSignature value) = 0 := by
  simp [doubledMagnusDegreeTwo, eventSignature]

/-- The degree-two Baker-Campbell-Hausdorff law. The logarithmic coordinate of
a chronological product gains exactly the commutator of the two degree-one
coordinates. -/
theorem doubled_magnus_degree_two_mul
    {A : Type u} [Ring A]
    (left right : StepTwoSignature A) :
    doubledMagnusDegreeTwo (left * right) =
      doubledMagnusDegreeTwo left +
        doubledMagnusDegreeTwo right +
        commutator left.degreeOne right.degreeOne := by
  rcases left with ⟨leftOne, leftTwo⟩
  rcases right with ⟨rightOne, rightTwo⟩
  change
    (leftTwo + 2 * (leftOne * rightOne) + rightTwo) -
        (leftOne + rightOne) * (leftOne + rightOne) =
      (leftTwo - leftOne * leftOne) +
        (rightTwo - rightOne * rightOne) +
        (leftOne * rightOne - rightOne * leftOne)
  noncomm_ring

/-- Chen concatenation followed by the degree-two logarithm is the truncated
BCH formula for two chronological words. -/
theorem doubled_magnus_degree_two_append
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A)
    (earlierWord laterWord : List Event) :
    doubledMagnusDegreeTwo
        (chronologicalSignature observe (earlierWord ++ laterWord)) =
      doubledMagnusDegreeTwo
          (chronologicalSignature observe earlierWord) +
        doubledMagnusDegreeTwo
          (chronologicalSignature observe laterWord) +
        commutator
          (chronologicalSignature observe earlierWord).degreeOne
          (chronologicalSignature observe laterWord).degreeOne := by
  rw [chronological_signature_append]
  exact doubled_magnus_degree_two_mul _ _

/-- For exactly two events, the doubled degree-two Magnus coordinate is their
commutator. -/
theorem doubled_magnus_two_events_eq_commutator
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (eventP eventQ : Event) :
    doubledMagnusDegreeTwo
        (chronologicalSignature observe [eventP, eventQ]) =
      commutator (observe eventP) (observe eventQ) := by
  have hPair :
      chronologicalSignature observe [eventP, eventQ] =
        eventSignature (observe eventP) *
          eventSignature (observe eventQ) := by
    simp [chronologicalSignature]
  rw [hPair, doubled_magnus_degree_two_mul]
  simp [doubledMagnusDegreeTwo, eventSignature]

/-- Reversing a two-event chronology reverses the orientation of its
degree-two logarithmic coordinate. -/
theorem doubled_magnus_two_events_swap
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (eventP eventQ : Event) :
    doubledMagnusDegreeTwo
        (chronologicalSignature observe [eventQ, eventP]) =
      -doubledMagnusDegreeTwo
        (chronologicalSignature observe [eventP, eventQ]) := by
  rw [doubled_magnus_two_events_eq_commutator,
    doubled_magnus_two_events_eq_commutator]
  change
    observe eventQ * observe eventP - observe eventP * observe eventQ =
      -(observe eventP * observe eventQ - observe eventQ * observe eventP)
  noncomm_ring

/-- A commuting pair has no degree-two chronological defect. -/
theorem doubled_magnus_two_events_eq_zero_of_commute
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (eventP eventQ : Event)
    (hCommute : observe eventP * observe eventQ =
      observe eventQ * observe eventP) :
    doubledMagnusDegreeTwo
        (chronologicalSignature observe [eventP, eventQ]) = 0 := by
  rw [doubled_magnus_two_events_eq_commutator]
  exact sub_eq_zero.mpr hCommute

#print axioms chronological_signature_append
#print axioms chronological_signature_degree_one
#print axioms doubled_magnus_degree_two_mul
#print axioms doubled_magnus_degree_two_append
#print axioms doubled_magnus_two_events_eq_commutator
#print axioms doubled_magnus_two_events_swap
#print axioms doubled_magnus_two_events_eq_zero_of_commute

end D5.S3.Observer.Chronology.StepTwoChronologicalSignature
