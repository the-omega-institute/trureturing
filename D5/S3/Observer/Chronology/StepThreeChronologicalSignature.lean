/- GID: D5/S3/Observer/Chronology/StepThreeChronologicalSignature
   generality: G
   mirror-B: none(waiver:new-library-node)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Step-three chronological signatures obey Chen composition, truncate multiplicatively to step two, and realize reverse-and-negate by an explicit antipode. -/

import D5.S3.Observer.Chronology.StepTwoChronologicalSignature
import Mathlib.Tactic

/-!
# Step-three chronological signatures

A finite event word is recorded through degree three using the denominator-free
coordinates

`(X₁, 2 X₂, 6 X₃)`.

Chen composition is therefore

`Z₁ = X₁ + Y₁`,

`2 Z₂ = 2 X₂ + 2 X₁Y₁ + 2 Y₂`,

`6 Z₃ = 6 X₃ + 3 (2 X₂)Y₁ + 3 X₁(2 Y₂) + 6 Y₃`.

The first two coordinates recover the frozen step-two signature through a
monoid homomorphism. Over a ring, an explicit antipode is both a left and a
right inverse for Chen composition and reverses the order of a product.
Consequently reversing an event word and negating each event realizes the
antipode through degree three.

This file constructs the finite algebraic truncation. It does not construct a
completed tensor Hopf algebra, prove analytic Magnus convergence, or claim that
three levels recover every event chronology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.StepThreeChronologicalSignature

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature

universe u v

/-- Degree one, twice degree two, and six times degree three of a chronological
signature. The factorial normalization avoids division. -/
@[ext]
structure StepThreeSignature (A : Type u) where
  degreeOne : A
  doubledDegreeTwo : A
  sextupledDegreeThree : A

namespace StepThreeSignature

variable {A : Type u}

/-- Chen composition through degree three. Every event in the left input is
earlier than every event in the right input. -/
def compose [Semiring A]
    (left right : StepThreeSignature A) : StepThreeSignature A where
  degreeOne := left.degreeOne + right.degreeOne
  doubledDegreeTwo :=
    left.doubledDegreeTwo +
      2 * (left.degreeOne * right.degreeOne) +
      right.doubledDegreeTwo
  sextupledDegreeThree :=
    left.sextupledDegreeThree +
      3 * (left.doubledDegreeTwo * right.degreeOne) +
      3 * (left.degreeOne * right.doubledDegreeTwo) +
      right.sextupledDegreeThree

/-- Empty chronological signature. -/
def identity [Zero A] : StepThreeSignature A where
  degreeOne := 0
  doubledDegreeTwo := 0
  sextupledDegreeThree := 0

/-- Chen composition through degree three is associative. -/
instance [Semiring A] : Monoid (StepThreeSignature A) where
  one := identity
  mul := compose
  one_mul signature := by
    rcases signature with ⟨degreeOne, degreeTwo, degreeThree⟩
    ext <;> simp [compose, identity]
  mul_one signature := by
    rcases signature with ⟨degreeOne, degreeTwo, degreeThree⟩
    ext <;> simp [compose, identity]
  mul_assoc left middle right := by
    rcases left with ⟨leftOne, leftTwo, leftThree⟩
    rcases middle with ⟨middleOne, middleTwo, middleThree⟩
    rcases right with ⟨rightOne, rightTwo, rightThree⟩
    ext <;>
      simp [compose, mul_add, add_mul, mul_assoc] <;>
      noncomm_ring

@[simp]
theorem degreeOne_one [Semiring A] :
    (1 : StepThreeSignature A).degreeOne = 0 := by
  rfl

@[simp]
theorem doubledDegreeTwo_one [Semiring A] :
    (1 : StepThreeSignature A).doubledDegreeTwo = 0 := by
  rfl

@[simp]
theorem sextupledDegreeThree_one [Semiring A] :
    (1 : StepThreeSignature A).sextupledDegreeThree = 0 := by
  rfl

@[simp]
theorem degreeOne_mul [Semiring A]
    (left right : StepThreeSignature A) :
    (left * right).degreeOne = left.degreeOne + right.degreeOne := by
  rfl

@[simp]
theorem doubledDegreeTwo_mul [Semiring A]
    (left right : StepThreeSignature A) :
    (left * right).doubledDegreeTwo =
      left.doubledDegreeTwo +
        2 * (left.degreeOne * right.degreeOne) +
        right.doubledDegreeTwo := by
  rfl

@[simp]
theorem sextupledDegreeThree_mul [Semiring A]
    (left right : StepThreeSignature A) :
    (left * right).sextupledDegreeThree =
      left.sextupledDegreeThree +
        3 * (left.doubledDegreeTwo * right.degreeOne) +
        3 * (left.degreeOne * right.doubledDegreeTwo) +
        right.sextupledDegreeThree := by
  rfl

end StepThreeSignature

/-- Truncated exponential of one event through degree three. -/
def eventStepThreeSignature
    {A : Type u} [Semiring A] (value : A) : StepThreeSignature A where
  degreeOne := value
  doubledDegreeTwo := value * value
  sextupledDegreeThree := value * value * value

/-- Step-three signature of an event list read from left to right. -/
def chronologicalStepThreeSignature
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A) : List Event → StepThreeSignature A
  | [] => 1
  | event :: events =>
      eventStepThreeSignature (observe event) *
        chronologicalStepThreeSignature observe events

@[simp]
theorem chronological_step_three_signature_nil
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A) :
    chronologicalStepThreeSignature observe [] = 1 := by
  rfl

@[simp]
theorem chronological_step_three_signature_cons
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A) (event : Event) (events : List Event) :
    chronologicalStepThreeSignature observe (event :: events) =
      eventStepThreeSignature (observe event) *
        chronologicalStepThreeSignature observe events := by
  rfl

/-- Chen concatenation identity through degree three. -/
theorem chronological_step_three_signature_append
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A)
    (earlierWord laterWord : List Event) :
    chronologicalStepThreeSignature observe (earlierWord ++ laterWord) =
      chronologicalStepThreeSignature observe earlierWord *
        chronologicalStepThreeSignature observe laterWord := by
  induction earlierWord with
  | nil =>
      simp [chronologicalStepThreeSignature]
  | cons event earlierWord inductionHypothesis =>
      simp [chronologicalStepThreeSignature, inductionHypothesis, mul_assoc]

/-- Forget degree three and retain the frozen step-two signature. -/
def truncateStepTwo
    {A : Type u} (signature : StepThreeSignature A) : StepTwoSignature A where
  degreeOne := signature.degreeOne
  doubledDegreeTwo := signature.doubledDegreeTwo

@[simp]
theorem truncate_step_two_one
    {A : Type u} [Semiring A] :
    truncateStepTwo (1 : StepThreeSignature A) =
      (1 : StepTwoSignature A) := by
  rfl

@[simp]
theorem truncate_step_two_mul
    {A : Type u} [Semiring A]
    (left right : StepThreeSignature A) :
    truncateStepTwo (left * right) =
      truncateStepTwo left * truncateStepTwo right := by
  rfl

/-- Degree-three truncation to degree two is a monoid homomorphism. -/
def truncateStepTwoHom
    (A : Type u) [Semiring A] :
    StepThreeSignature A →* StepTwoSignature A where
  toFun := truncateStepTwo
  map_one' := truncate_step_two_one
  map_mul' := truncate_step_two_mul

@[simp]
theorem truncate_event_step_three_signature
    {A : Type u} [Semiring A] (value : A) :
    truncateStepTwo (eventStepThreeSignature value) =
      eventSignature value := by
  rfl

/-- Truncating a chronological step-three word recovers its complete frozen
step-two chronological signature. -/
theorem truncate_chronological_step_three_signature
    {Event : Type v} {A : Type u} [Semiring A]
    (observe : Event → A) (events : List Event) :
    truncateStepTwo (chronologicalStepThreeSignature observe events) =
      chronologicalSignature observe events := by
  induction events with
  | nil =>
      rfl
  | cons event events inductionHypothesis =>
      rw [chronological_step_three_signature_cons,
        truncate_step_two_mul,
        truncate_event_step_three_signature,
        inductionHypothesis]
      rfl

/-- Explicit antipode through degree three in factorial coordinates. -/
def stepThreeAntipode
    {A : Type u} [Ring A]
    (signature : StepThreeSignature A) : StepThreeSignature A where
  degreeOne := -signature.degreeOne
  doubledDegreeTwo :=
    2 * (signature.degreeOne * signature.degreeOne) -
      signature.doubledDegreeTwo
  sextupledDegreeThree :=
    -signature.sextupledDegreeThree +
      3 * (signature.doubledDegreeTwo * signature.degreeOne) +
      3 * (signature.degreeOne * signature.doubledDegreeTwo) -
      6 * (signature.degreeOne * signature.degreeOne * signature.degreeOne)

@[simp]
theorem step_three_antipode_one
    {A : Type u} [Ring A] :
    stepThreeAntipode (1 : StepThreeSignature A) = 1 := by
  ext <;> simp [stepThreeAntipode]

/-- The antipode is a right inverse for Chen composition. -/
theorem mul_step_three_antipode
    {A : Type u} [Ring A] (signature : StepThreeSignature A) :
    signature * stepThreeAntipode signature = 1 := by
  rcases signature with ⟨degreeOne, degreeTwo, degreeThree⟩
  ext <;>
    simp [stepThreeAntipode, StepThreeSignature.compose] <;>
    noncomm_ring

/-- The antipode is also a left inverse for Chen composition. -/
theorem step_three_antipode_mul
    {A : Type u} [Ring A] (signature : StepThreeSignature A) :
    stepThreeAntipode signature * signature = 1 := by
  rcases signature with ⟨degreeOne, degreeTwo, degreeThree⟩
  ext <;>
    simp [stepThreeAntipode, StepThreeSignature.compose] <;>
    noncomm_ring

/-- The step-three antipode reverses chronological multiplication order. -/
theorem step_three_antipode_mul_rev
    {A : Type u} [Ring A]
    (left right : StepThreeSignature A) :
    stepThreeAntipode (left * right) =
      stepThreeAntipode right * stepThreeAntipode left := by
  rcases left with ⟨leftOne, leftTwo, leftThree⟩
  rcases right with ⟨rightOne, rightTwo, rightThree⟩
  ext <;>
    simp [stepThreeAntipode, StepThreeSignature.compose] <;>
    noncomm_ring

/-- Negating one event realizes its step-three antipode. -/
theorem step_three_antipode_event
    {A : Type u} [Ring A] (value : A) :
    stepThreeAntipode (eventStepThreeSignature value) =
      eventStepThreeSignature (-value) := by
  ext <;>
    simp [stepThreeAntipode, eventStepThreeSignature] <;>
    noncomm_ring

/-- Reverse-and-negate realizes chronological time reversal through degree
three. -/
theorem chronological_step_three_reverse_neg
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    chronologicalStepThreeSignature
        (fun event => -observe event) events.reverse =
      stepThreeAntipode
        (chronologicalStepThreeSignature observe events) := by
  induction events with
  | nil =>
      simp
  | cons event events inductionHypothesis =>
      calc
        chronologicalStepThreeSignature
            (fun item => -observe item) (event :: events).reverse =
          chronologicalStepThreeSignature
              (fun item => -observe item) events.reverse *
            eventStepThreeSignature (-observe event) := by
              rw [List.reverse_cons,
                chronological_step_three_signature_append]
              simp
        _ = stepThreeAntipode
              (chronologicalStepThreeSignature observe events) *
            stepThreeAntipode
              (eventStepThreeSignature (observe event)) := by
              rw [inductionHypothesis, step_three_antipode_event]
        _ = stepThreeAntipode
              (eventStepThreeSignature (observe event) *
                chronologicalStepThreeSignature observe events) := by
              symm
              exact step_three_antipode_mul_rev
                (eventStepThreeSignature (observe event))
                (chronologicalStepThreeSignature observe events)
        _ = stepThreeAntipode
              (chronologicalStepThreeSignature observe (event :: events)) := by
              rfl

#print axioms chronological_step_three_signature_append
#print axioms truncate_chronological_step_three_signature
#print axioms mul_step_three_antipode
#print axioms step_three_antipode_mul
#print axioms step_three_antipode_mul_rev
#print axioms chronological_step_three_reverse_neg

end D5.S3.Observer.Chronology.StepThreeChronologicalSignature
