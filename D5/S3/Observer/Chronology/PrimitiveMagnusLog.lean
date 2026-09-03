/- GID: D5/S3/Observer/Chronology/PrimitiveMagnusLog
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/PrimitiveMagnusLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The step-two tensor logarithm is an antisymmetric primitive coordinate. -/

import D5.S3.Observer.Chronology.TruncatedTensorHopf
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Primitive step-two Magnus logarithm

For a doubled step-two tensor signature `(x,D)`, the degree-two Magnus
coordinate is

`D - x ⊗ₜ x`.

Its chronological multiplication law adds the two prior logarithmic
coordinates and the tensor commutator of the degree-one components. For a
group-like signature, the standard degree-two balance

`D + flip D = 2 • (x ⊗ₜ x)`

forces this logarithmic coordinate to be antisymmetric under the canonical
tensor flip. Thus it is exactly the degree-two primitive direction expected
from the logarithm of a group-like tensor signature.

This module stays inside the genuine tensor square and uses the canonical
Mathlib tensor symmetry. It does not identify the antisymmetric tensor square
with the full free Lie algebra in every characteristic, construct an infinite
formal logarithm, or prove analytic Magnus convergence. A later representation
bridge maps this universal tensor commutator into ring and operator
commutators.
-/

/- Library-search audit trail (2026-09-01):
   * `TruncatedTensorSignature` owns Chen multiplication in `V ⊗[R] V`.
   * `TruncatedTensorHopf` owns the exact doubled degree-two group-like balance.
   * Pinned Mathlib supplies the tensor-factor commutor, subtraction in tensor
     modules, and the free Lie algebra API used by the next bridge.
   * `StepTwoChronologicalLogarithm` owns the already frozen represented BCH
     shadow in one noncommutative ring. The present owner precedes any such
     representation and therefore does not redefine that object.
   * Repository search found no owner of this universal primitive tensor
     logarithm or its antisymmetry theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open TensorProduct

namespace D5.S3.Observer.Chronology.PrimitiveMagnusLog

open D5.S3.Observer.Chronology.TruncatedTensorSignature
open D5.S3.Observer.Chronology.TruncatedTensorHopf

universe u v w

variable (R : Type u) (V : Type v)
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- The universal degree-two Lie bracket before choosing a representation. -/
def tensorCommutator (left right : V) : V ⊗[R] V :=
  left ⊗ₜ[R] right - right ⊗ₜ[R] left

/-- Twice the degree-two primitive logarithmic coordinate. -/
def doubledPrimitiveMagnus
    (signature : TensorSignature R V) : V ⊗[R] V :=
  signature.doubledDegreeTwo -
    signature.degreeOne ⊗ₜ[R] signature.degreeOne

/-- Antisymmetry under the canonical tensor flip. -/
def IsPrimitiveDegreeTwo (tensor : V ⊗[R] V) : Prop :=
  tensorFlip R V tensor = -tensor

/-- The universal tensor commutator is antisymmetric. -/
theorem tensor_commutator_is_primitive
    (left right : V) :
    IsPrimitiveDegreeTwo R V (tensorCommutator R V left right) := by
  unfold IsPrimitiveDegreeTwo tensorCommutator tensorFlip
  rw [map_sub, TensorProduct.comm_tmul, TensorProduct.comm_tmul]
  abel

/-- A single event has no degree-two primitive logarithm. -/
theorem doubled_primitive_magnus_event
    (value : V) :
    doubledPrimitiveMagnus R V (eventTensorSignature R V value) = 0 := by
  simp [doubledPrimitiveMagnus, eventTensorSignature]

/-- The tensor-level step-two BCH law. -/
theorem doubled_primitive_magnus_mul
    (left right : TensorSignature R V) :
    doubledPrimitiveMagnus R V (left * right) =
      doubledPrimitiveMagnus R V left +
        doubledPrimitiveMagnus R V right +
        tensorCommutator R V left.degreeOne right.degreeOne := by
  rcases left with ⟨leftOne, leftTwo⟩
  rcases right with ⟨rightOne, rightTwo⟩
  change
    (leftTwo + 2 • (leftOne ⊗ₜ[R] rightOne) + rightTwo) -
        ((leftOne + rightOne) ⊗ₜ[R] (leftOne + rightOne)) =
      (leftTwo - leftOne ⊗ₜ[R] leftOne) +
        (rightTwo - rightOne ⊗ₜ[R] rightOne) +
        (leftOne ⊗ₜ[R] rightOne - rightOne ⊗ₜ[R] leftOne)
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, two_nsmul]
  abel

/-- Chen concatenation becomes the tensor BCH law after the primitive
logarithm is taken. -/
theorem doubled_primitive_magnus_append
    {Event : Type w} (observe : Event → V)
    (earlierWord laterWord : List Event) :
    doubledPrimitiveMagnus R V
        (chronologicalTensorSignature R V observe
          (earlierWord ++ laterWord)) =
      doubledPrimitiveMagnus R V
          (chronologicalTensorSignature R V observe earlierWord) +
        doubledPrimitiveMagnus R V
          (chronologicalTensorSignature R V observe laterWord) +
        tensorCommutator R V
          (chronologicalTensorSignature R V observe earlierWord).degreeOne
          (chronologicalTensorSignature R V observe laterWord).degreeOne := by
  rw [chronological_tensor_signature_append]
  exact doubled_primitive_magnus_mul R V _ _

/-- Two events produce exactly their antisymmetric tensor bracket. -/
theorem doubled_primitive_magnus_two_events
    (left right : V) :
    doubledPrimitiveMagnus R V
        (chronologicalTensorSignature R V
          (fun value : V => value) [left, right]) =
      tensorCommutator R V left right := by
  rw [chronological_tensor_signature_two_events]
  unfold doubledPrimitiveMagnus tensorCommutator
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, two_nsmul]
  abel

/-- Reversing a two-event chronology negates its primitive degree-two
coordinate. -/
theorem doubled_primitive_magnus_two_events_swap
    (left right : V) :
    doubledPrimitiveMagnus R V
        (chronologicalTensorSignature R V
          (fun value : V => value) [right, left]) =
      -doubledPrimitiveMagnus R V
        (chronologicalTensorSignature R V
          (fun value : V => value) [left, right]) := by
  rw [doubled_primitive_magnus_two_events,
    doubled_primitive_magnus_two_events]
  unfold tensorCommutator
  abel

/-- The logarithm of a step-two group-like signature is antisymmetric and
therefore primitive at degree two. -/
theorem group_like_doubled_primitive_magnus
    (signature : TensorSignature R V)
    (groupLike : IsStepTwoGroupLike R V signature) :
    IsPrimitiveDegreeTwo R V
      (doubledPrimitiveMagnus R V signature) := by
  rcases signature with ⟨degreeOne, degreeTwo⟩
  change
    degreeTwo + tensorFlip R V degreeTwo =
      2 • (degreeOne ⊗ₜ[R] degreeOne) at groupLike
  have flippedDegreeTwo :
      tensorFlip R V degreeTwo =
        2 • (degreeOne ⊗ₜ[R] degreeOne) - degreeTwo := by
    rw [← groupLike]
    abel
  unfold IsPrimitiveDegreeTwo doubledPrimitiveMagnus
  rw [map_sub, tensor_flip_tmul, flippedDegreeTwo]
  simp only [two_nsmul]
  abel

/-- Every finite chronological word has a primitive degree-two Magnus
coordinate. -/
theorem chronological_primitive_magnus
    {Event : Type w} (observe : Event → V) (events : List Event) :
    IsPrimitiveDegreeTwo R V
      (doubledPrimitiveMagnus R V
        (chronologicalTensorSignature R V observe events)) := by
  exact group_like_doubled_primitive_magnus R V _
    (chronological_tensor_signature_is_step_two_group_like
      R V observe events)

#print axioms tensor_commutator_is_primitive
#print axioms doubled_primitive_magnus_event
#print axioms doubled_primitive_magnus_mul
#print axioms doubled_primitive_magnus_append
#print axioms doubled_primitive_magnus_two_events
#print axioms doubled_primitive_magnus_two_events_swap
#print axioms group_like_doubled_primitive_magnus
#print axioms chronological_primitive_magnus

end D5.S3.Observer.Chronology.PrimitiveMagnusLog
