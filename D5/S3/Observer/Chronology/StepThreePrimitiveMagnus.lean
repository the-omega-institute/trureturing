/- GID: D5/S3/Observer/Chronology/StepThreePrimitiveMagnus
   generality: G
   mirror-B: none(waiver:new-library-node)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The denominator-free third Magnus coordinate obeys the exact degree-three BCH law and changes sign under the step-three antipode. -/

import D5.S3.Observer.Chronology.StepThreeChronologicalSignature
import Mathlib.Tactic

/-!
# Primitive Magnus coordinates through degree three

For a step-three signature with factorial coordinates `(X₁, 2 X₂, 6 X₃)`, the
integral normalization of the degree-three logarithm is

`12 Ω₃ = 2 (6 X₃) - 3 (X₁ (2 X₂) + (2 X₂) X₁) + 4 X₁³`.

This coordinate vanishes on a single event. Under Chen composition it obeys
the exact degree-three BCH law. Besides the two existing third coordinates,
the correction consists of commutators between first- and second-degree
Magnus coordinates and the two standard nested commutators

`[x,[x,y]] + [y,[y,x]]`.

The explicit step-three antipode negates both primitive Magnus coordinates.
Thus chronological reverse-and-negate reverses the sign of the degree-three
primitive while retaining its magnitude in normed representations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.StepThreePrimitiveMagnus

open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepThreeChronologicalSignature

universe u v

/-- The doubled degree-two Magnus coordinate of a step-three signature. -/
def doubledMagnusDegreeTwoOfStepThree
    {A : Type u} [Ring A] (signature : StepThreeSignature A) : A :=
  doubledMagnusDegreeTwo (truncateStepTwo signature)

/-- Twelve times the degree-three primitive logarithmic coordinate. -/
def duodecupledMagnusDegreeThree
    {A : Type u} [Ring A] (signature : StepThreeSignature A) : A :=
  2 * signature.sextupledDegreeThree -
    3 *
      (signature.degreeOne * signature.doubledDegreeTwo +
        signature.doubledDegreeTwo * signature.degreeOne) +
    4 *
      (signature.degreeOne * signature.degreeOne * signature.degreeOne)

/-- A single event has no degree-two logarithmic chronology. -/
@[simp]
theorem doubled_magnus_degree_two_step_three_event
    {A : Type u} [Ring A] (value : A) :
    doubledMagnusDegreeTwoOfStepThree
        (eventStepThreeSignature value) = 0 := by
  simp [doubledMagnusDegreeTwoOfStepThree]

/-- A single event also has no degree-three logarithmic chronology. -/
@[simp]
theorem duodecupled_magnus_degree_three_event
    {A : Type u} [Ring A] (value : A) :
    duodecupledMagnusDegreeThree
        (eventStepThreeSignature value) = 0 := by
  simp [duodecupledMagnusDegreeThree, eventStepThreeSignature]
  noncomm_ring

/-- The exact degree-three Baker-Campbell-Hausdorff law in denominator-free
coordinates. -/
theorem duodecupled_magnus_degree_three_mul
    {A : Type u} [Ring A]
    (left right : StepThreeSignature A) :
    duodecupledMagnusDegreeThree (left * right) =
      duodecupledMagnusDegreeThree left +
        duodecupledMagnusDegreeThree right +
        3 * commutator
          (doubledMagnusDegreeTwoOfStepThree left) right.degreeOne +
        3 * commutator left.degreeOne
          (doubledMagnusDegreeTwoOfStepThree right) +
        commutator left.degreeOne
          (commutator left.degreeOne right.degreeOne) +
        commutator right.degreeOne
          (commutator right.degreeOne left.degreeOne) := by
  rcases left with ⟨leftOne, leftTwo, leftThree⟩
  rcases right with ⟨rightOne, rightTwo, rightThree⟩
  simp [duodecupledMagnusDegreeThree,
    doubledMagnusDegreeTwoOfStepThree, truncateStepTwo,
    doubledMagnusDegreeTwo, StepThreeSignature.compose, commutator]
  noncomm_ring

/-- The degree-two primitive changes sign under the step-three antipode. -/
theorem doubled_magnus_degree_two_step_three_antipode
    {A : Type u} [Ring A] (signature : StepThreeSignature A) :
    doubledMagnusDegreeTwoOfStepThree (stepThreeAntipode signature) =
      -doubledMagnusDegreeTwoOfStepThree signature := by
  rcases signature with ⟨degreeOne, degreeTwo, degreeThree⟩
  simp [doubledMagnusDegreeTwoOfStepThree, truncateStepTwo,
    doubledMagnusDegreeTwo, stepThreeAntipode]
  noncomm_ring

/-- The degree-three primitive also changes sign under the antipode. -/
theorem duodecupled_magnus_degree_three_antipode
    {A : Type u} [Ring A] (signature : StepThreeSignature A) :
    duodecupledMagnusDegreeThree (stepThreeAntipode signature) =
      -duodecupledMagnusDegreeThree signature := by
  rcases signature with ⟨degreeOne, degreeTwo, degreeThree⟩
  simp [duodecupledMagnusDegreeThree, stepThreeAntipode]
  noncomm_ring

/-- Chronological reverse-and-negate reverses the degree-three primitive
orientation. -/
theorem duodecupled_magnus_chronological_reverse_neg
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature
          (fun event => -observe event) events.reverse) =
      -duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature observe events) := by
  rw [chronological_step_three_reverse_neg,
    duodecupled_magnus_degree_three_antipode]

#print axioms duodecupled_magnus_degree_three_event
#print axioms duodecupled_magnus_degree_three_mul
#print axioms doubled_magnus_degree_two_step_three_antipode
#print axioms duodecupled_magnus_degree_three_antipode
#print axioms duodecupled_magnus_chronological_reverse_neg

end D5.S3.Observer.Chronology.StepThreePrimitiveMagnus
