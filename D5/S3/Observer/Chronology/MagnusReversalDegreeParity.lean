/- GID: D5/S3/Observer/Chronology/MagnusReversalDegreeParity
   generality: G
   mirror-B: none(waiver:new-library-node)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Plain word reversal negates the second Magnus primitive and preserves the third, realizing the first two cases of the homogeneous sign law (-1)^(degree+1). -/

import D5.S3.Observer.Chronology.StepThreePrimitiveMagnus
import Mathlib.Tactic

/-!
# Magnus parity under plain chronological reversal

Reverse-and-negate is the Chen antipode. Plain word reversal differs from that
operation by negating every event without changing its position. On factorial
signature coordinates, event negation acts by the grading involution

`(X₁, 2 X₂, 6 X₃) ↦ (-X₁, 2 X₂, -6 X₃)`.

The grading involution preserves the second Magnus primitive and negates the
third. The antipode negates every primitive degree. Combining the two actions
shows that plain word reversal

- negates the degree-two Magnus coordinate;
- preserves the degree-three Magnus coordinate.

These are the degree-two and degree-three cases of the homogeneous reversal
sign `(-1)^(n+1)`. This parity concerns Lie degree. It is distinct from prime
factor parity, Zeckendorf least-index parity, and odd/even restoration of an
involutive observer coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.MagnusReversalDegreeParity

open D5.S3.Observer.Chronology.StepThreeChronologicalSignature
open D5.S3.Observer.Chronology.StepThreePrimitiveMagnus

universe u v

/-- Negation of every primitive event acts by the homogeneous grading
involution through degree three. -/
def stepThreeGradeNegation
    {A : Type u} [Ring A]
    (signature : StepThreeSignature A) : StepThreeSignature A where
  degreeOne := -signature.degreeOne
  doubledDegreeTwo := signature.doubledDegreeTwo
  sextupledDegreeThree := -signature.sextupledDegreeThree

@[simp]
theorem step_three_grade_negation_one
    {A : Type u} [Ring A] :
    stepThreeGradeNegation (1 : StepThreeSignature A) = 1 := by
  ext <;> simp [stepThreeGradeNegation]

/-- The grading involution respects Chen multiplication. -/
theorem step_three_grade_negation_mul
    {A : Type u} [Ring A]
    (left right : StepThreeSignature A) :
    stepThreeGradeNegation (left * right) =
      stepThreeGradeNegation left * stepThreeGradeNegation right := by
  rcases left with ⟨leftOne, leftTwo, leftThree⟩
  rcases right with ⟨rightOne, rightTwo, rightThree⟩
  ext <;>
    simp [stepThreeGradeNegation, StepThreeSignature.compose] <;>
    noncomm_ring

/-- The grading action is a monoid endomorphism. -/
def stepThreeGradeNegationHom
    (A : Type u) [Ring A] :
    StepThreeSignature A →* StepThreeSignature A where
  toFun := stepThreeGradeNegation
  map_one' := step_three_grade_negation_one
  map_mul' := step_three_grade_negation_mul

/-- Grading a one-event signature is exactly negating that event. -/
theorem step_three_grade_negation_event
    {A : Type u} [Ring A] (value : A) :
    stepThreeGradeNegation (eventStepThreeSignature value) =
      eventStepThreeSignature (-value) := by
  ext <;>
    simp [stepThreeGradeNegation, eventStepThreeSignature] <;>
    noncomm_ring

/-- Negating every observation without reversing the word applies the grading
involution to its complete step-three signature. -/
theorem chronological_step_three_observation_negation
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    chronologicalStepThreeSignature
        (fun event => -observe event) events =
      stepThreeGradeNegation
        (chronologicalStepThreeSignature observe events) := by
  induction events with
  | nil =>
      simp
  | cons event events inductionHypothesis =>
      calc
        chronologicalStepThreeSignature
            (fun item => -observe item) (event :: events) =
          eventStepThreeSignature (-observe event) *
            chronologicalStepThreeSignature
              (fun item => -observe item) events := by
                rfl
        _ = stepThreeGradeNegation
              (eventStepThreeSignature (observe event)) *
            stepThreeGradeNegation
              (chronologicalStepThreeSignature observe events) := by
                rw [step_three_grade_negation_event,
                  inductionHypothesis]
        _ = stepThreeGradeNegation
              (eventStepThreeSignature (observe event) *
                chronologicalStepThreeSignature observe events) := by
                symm
                exact step_three_grade_negation_mul _ _
        _ = stepThreeGradeNegation
              (chronologicalStepThreeSignature observe (event :: events)) := by
                rfl

/-- Plain word reversal, followed by the grading involution, is the Chen
antipode. -/
theorem chronological_reverse_grade_eq_antipode
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    stepThreeGradeNegation
        (chronologicalStepThreeSignature observe events.reverse) =
      stepThreeAntipode
        (chronologicalStepThreeSignature observe events) := by
  calc
    stepThreeGradeNegation
        (chronologicalStepThreeSignature observe events.reverse) =
      chronologicalStepThreeSignature
        (fun event => -observe event) events.reverse :=
      (chronological_step_three_observation_negation
        observe events.reverse).symm
    _ = stepThreeAntipode
        (chronologicalStepThreeSignature observe events) :=
      chronological_step_three_reverse_neg observe events

/-- The grading involution preserves the degree-two Magnus primitive. -/
theorem doubled_magnus_grade_negation
    {A : Type u} [Ring A] (signature : StepThreeSignature A) :
    doubledMagnusDegreeTwoOfStepThree
        (stepThreeGradeNegation signature) =
      doubledMagnusDegreeTwoOfStepThree signature := by
  rcases signature with ⟨degreeOne, degreeTwo, degreeThree⟩
  simp [doubledMagnusDegreeTwoOfStepThree, truncateStepTwo,
    StepTwoChronologicalSignature.doubledMagnusDegreeTwo,
    stepThreeGradeNegation]
  noncomm_ring

/-- The grading involution negates the degree-three Magnus primitive. -/
theorem duodecupled_magnus_grade_negation
    {A : Type u} [Ring A] (signature : StepThreeSignature A) :
    duodecupledMagnusDegreeThree
        (stepThreeGradeNegation signature) =
      -duodecupledMagnusDegreeThree signature := by
  rcases signature with ⟨degreeOne, degreeTwo, degreeThree⟩
  simp [duodecupledMagnusDegreeThree, stepThreeGradeNegation]
  noncomm_ring

/-- Plain chronology reversal negates the degree-two primitive. -/
theorem doubled_magnus_plain_reverse
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    doubledMagnusDegreeTwoOfStepThree
        (chronologicalStepThreeSignature observe events.reverse) =
      -doubledMagnusDegreeTwoOfStepThree
        (chronologicalStepThreeSignature observe events) := by
  have hsignature := chronological_reverse_grade_eq_antipode observe events
  have hcoordinate := congrArg
    (doubledMagnusDegreeTwoOfStepThree (A := A)) hsignature
  rw [doubled_magnus_grade_negation,
    doubled_magnus_degree_two_step_three_antipode] at hcoordinate
  exact hcoordinate

/-- Plain chronology reversal preserves the degree-three primitive. -/
theorem duodecupled_magnus_plain_reverse
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature observe events.reverse) =
      duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature observe events) := by
  have hsignature := chronological_reverse_grade_eq_antipode observe events
  have hcoordinate := congrArg
    (duodecupledMagnusDegreeThree (A := A)) hsignature
  rw [duodecupled_magnus_grade_negation,
    duodecupled_magnus_degree_three_antipode] at hcoordinate
  exact neg_injective hcoordinate

/-- Headline degree-parity law for the first two nontrivial Magnus levels. -/
theorem chronological_reverse_magnus_degree_parity
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    doubledMagnusDegreeTwoOfStepThree
        (chronologicalStepThreeSignature observe events.reverse) =
        -doubledMagnusDegreeTwoOfStepThree
          (chronologicalStepThreeSignature observe events) ∧
      duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature observe events.reverse) =
        duodecupledMagnusDegreeThree
          (chronologicalStepThreeSignature observe events) :=
  ⟨doubled_magnus_plain_reverse observe events,
    duodecupled_magnus_plain_reverse observe events⟩

#print axioms step_three_grade_negation_mul
#print axioms chronological_step_three_observation_negation
#print axioms chronological_reverse_grade_eq_antipode
#print axioms doubled_magnus_plain_reverse
#print axioms duodecupled_magnus_plain_reverse
#print axioms chronological_reverse_magnus_degree_parity

end D5.S3.Observer.Chronology.MagnusReversalDegreeParity
