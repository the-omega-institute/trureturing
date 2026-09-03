/- GID: D5/S3/Observer/Chronology/StepTwoFreeLieBridge
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/StepTwoFreeLieBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tensor Magnus brackets map to represented commutators and free Lie brackets. -/

import D5.S3.Observer.Chronology.PrimitiveMagnusLog
import D5.S3.Observer.Chronology.StepTwoChronologicalSignature
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Step-two free Lie and representation bridge

The universal chronological signature stores degree two in a genuine tensor
square. The older step-two signature stores the same information after a
chosen associative-algebra representation has multiplied the two tensor
factors. This module connects the two owners using Mathlib's existing
multiplication map

`LinearMap.mul' R A : A ⊗[R] A →ₗ[R] A`.

It proves that tensor Chen multiplication maps to the frozen represented Chen
multiplication, and that the universal primitive Magnus coordinate maps to the
frozen ring-valued degree-two Magnus coordinate. The universal tensor bracket
therefore maps to the repository's standard ring commutator.

The module also uses Mathlib's `FreeLieAlgebra` universal property. A map from
event labels into an associative algebra extends uniquely to a Lie
homomorphism, and the bracket of two free generators evaluates to their ring
commutator.

No PBW theorem, injectivity of the free-Lie realization, all-degree tensor
Hopf algebra, completed enveloping algebra, or analytic Magnus convergence is
asserted.
-/

/- Library-search audit trail (2026-09-01):
   * `PrimitiveMagnusLog` owns the universal tensor commutator and primitive
     degree-two logarithm.
   * `StepTwoChronologicalSignature` owns the represented Chen/BCH shadow and
     imports the repository-wide commutator convention from
     `ProjectionCommutatorIdentity`.
   * Pinned Mathlib supplies `LinearMap.mul'`, its pure-tensor computation,
     `LieRing.ofAssociativeRing`, `LieAlgebra.ofAssociativeAlgebra`, and the
     universal `FreeLieAlgebra.lift`.
   * Repository search found no existing monoid representation from the
     universal tensor signature to the represented step-two signature, nor a
     bridge from its primitive tensor coordinate to the free Lie bracket. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open TensorProduct

namespace D5.S3.Observer.Chronology.StepTwoFreeLieBridge

open D5.S3.Observer.Chronology.TruncatedTensorSignature
open D5.S3.Observer.Chronology.PrimitiveMagnusLog
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

universe u v w

variable (R : Type u) (A : Type v)
variable [CommRing R] [Ring A] [Algebra R A]

/-- Multiply the two factors of a tensor in the chosen associative algebra. -/
def tensorMultiplication : A ⊗[R] A →ₗ[R] A :=
  LinearMap.mul' R A

@[simp]
theorem tensor_multiplication_tmul (left right : A) :
    tensorMultiplication R A (left ⊗ₜ[R] right) = left * right := by
  rfl

/-- Apply the associative-algebra representation to degree two of a universal
tensor signature. -/
def representTensorSignature
    (signature : TensorSignature R A) : StepTwoSignature A where
  degreeOne := signature.degreeOne
  doubledDegreeTwo :=
    tensorMultiplication R A signature.doubledDegreeTwo

/-- A universal single-event signature maps to the frozen represented event
signature. -/
theorem represent_event_tensor_signature (value : A) :
    representTensorSignature R A (eventTensorSignature R A value) =
      eventSignature value := by
  ext <;>
    simp [representTensorSignature, eventTensorSignature,
      eventSignature, tensorMultiplication]

/-- The tensor representation preserves chronological multiplication. -/
theorem represent_tensor_signature_mul
    (left right : TensorSignature R A) :
    representTensorSignature R A (left * right) =
      representTensorSignature R A left *
        representTensorSignature R A right := by
  rcases left with ⟨leftOne, leftTwo⟩
  rcases right with ⟨rightOne, rightTwo⟩
  ext
  · rfl
  · change
      tensorMultiplication R A
          (leftTwo + 2 • (leftOne ⊗ₜ[R] rightOne) + rightTwo) =
        tensorMultiplication R A leftTwo +
          2 * (leftOne * rightOne) +
          tensorMultiplication R A rightTwo
    simp [tensorMultiplication, two_mul]

/-- The universal-to-represented map is a monoid homomorphism. -/
def tensorSignatureRepresentation :
    TensorSignature R A →* StepTwoSignature A where
  toFun := representTensorSignature R A
  map_one' := by
    ext <;> simp [representTensorSignature, tensorMultiplication]
  map_mul' := represent_tensor_signature_mul R A

/-- Representation commutes with the finite chronological word fold. -/
theorem represent_chronological_tensor_signature
    {Event : Type w} (observe : Event → A) (events : List Event) :
    representTensorSignature R A
        (chronologicalTensorSignature R A observe events) =
      chronologicalSignature observe events := by
  induction events with
  | nil =>
      change representTensorSignature R A (1 : TensorSignature R A) =
        (1 : StepTwoSignature A)
      exact (tensorSignatureRepresentation R A).map_one
  | cons event events inductionHypothesis =>
      rw [chronological_tensor_signature_cons,
        chronological_signature_cons,
        represent_tensor_signature_mul,
        represent_event_tensor_signature,
        inductionHypothesis]

/-- Multiplication sends the universal tensor bracket to the repository's
standard associative commutator. -/
theorem tensor_multiplication_commutator
    (left right : A) :
    tensorMultiplication R A (tensorCommutator R A left right) =
      commutator left right := by
  unfold tensorCommutator
  rw [map_sub, tensor_multiplication_tmul,
    tensor_multiplication_tmul]
  rfl

/-- The universal primitive Magnus coordinate maps to the frozen represented
Magnus coordinate. -/
theorem represent_doubled_primitive_magnus
    (signature : TensorSignature R A) :
    tensorMultiplication R A
        (doubledPrimitiveMagnus R A signature) =
      doubledMagnusDegreeTwo
        (representTensorSignature R A signature) := by
  rcases signature with ⟨degreeOne, degreeTwo⟩
  simp [tensorMultiplication, doubledPrimitiveMagnus,
    doubledMagnusDegreeTwo, representTensorSignature]

/-- The complete two-event tensor logarithm maps to the represented
commutator theorem. -/
theorem represent_two_event_primitive_magnus
    (left right : A) :
    tensorMultiplication R A
        (doubledPrimitiveMagnus R A
          (chronologicalTensorSignature R A
            (fun value : A => value) [left, right])) =
      commutator left right := by
  rw [doubled_primitive_magnus_two_events]
  exact tensor_multiplication_commutator R A left right

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra

/-- The universal Lie-algebra evaluation extending a map on event labels. -/
noncomputable def freeLieEvaluation
    {Event : Type w} (observe : Event → A) :
    FreeLieAlgebra R Event →ₗ⁅R⁆ A :=
  FreeLieAlgebra.lift R observe

@[simp]
theorem free_lie_evaluation_generator
    {Event : Type w} (observe : Event → A) (event : Event) :
    freeLieEvaluation R A observe (FreeLieAlgebra.of R event) =
      observe event := by
  simp [freeLieEvaluation]

/-- A bracket of two free generators evaluates to the associative ring
commutator of their observed values. -/
theorem free_lie_evaluation_bracket
    {Event : Type w} (observe : Event → A)
    (left right : Event) :
    freeLieEvaluation R A observe
        ⁅FreeLieAlgebra.of R left, FreeLieAlgebra.of R right⁆ =
      commutator (observe left) (observe right) := by
  rw [LieHom.map_lie,
    free_lie_evaluation_generator,
    free_lie_evaluation_generator]
  rfl

/-- The tensor and free-Lie realizations of a two-event bracket have the same
value in every associative-algebra representation. -/
theorem tensor_and_free_lie_brackets_agree
    {Event : Type w} (observe : Event → A)
    (left right : Event) :
    tensorMultiplication R A
        (tensorCommutator R A (observe left) (observe right)) =
      freeLieEvaluation R A observe
        ⁅FreeLieAlgebra.of R left, FreeLieAlgebra.of R right⁆ := by
  rw [tensor_multiplication_commutator,
    free_lie_evaluation_bracket]

#print axioms tensor_multiplication_tmul
#print axioms represent_event_tensor_signature
#print axioms represent_tensor_signature_mul
#print axioms represent_chronological_tensor_signature
#print axioms tensor_multiplication_commutator
#print axioms represent_doubled_primitive_magnus
#print axioms represent_two_event_primitive_magnus
#print axioms free_lie_evaluation_generator
#print axioms free_lie_evaluation_bracket
#print axioms tensor_and_free_lie_brackets_agree

end D5.S3.Observer.Chronology.StepTwoFreeLieBridge
