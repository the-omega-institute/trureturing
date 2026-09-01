/- GID: D5/S3/Observer/Chronology/TruncatedTensorHopf
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/TruncatedTensorHopf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tensor flip characterizes the group-like degree-two equation and preserves chronological Chen products. -/

import D5.S3.Observer.Chronology.TruncatedTensorSignature
import Mathlib.Tactic

/-!
# Truncated tensor group-like laws

The degree-two truncation of a normalized tensor signature is group-like
exactly when its symmetric tensor part is determined by degree one.  In the
doubled convention this equation is

`D + tau D = 2 • (x ⊗ x)`.

Here `tau` is the canonical tensor flip.  Single-event signatures satisfy the
equation, it is preserved by Chen multiplication, and therefore every finite
chronological word signature satisfies it.

This is the finite degree-two group-like equation inherited from the tensor
bialgebra.  This file does not manufacture a cartesian diagonal, and it does
not claim that the two-coordinate carrier itself is a Mathlib `HopfAlgebra`.
A full linear tensor algebra and its completion remain separate objects.
-/

/- Library-search audit trail (2026-09-01):
   * `TruncatedTensorSignature` owns the tensor carrier and Chen product.
   * The earlier `ChronologicalSignatureHopf` candidate packages a cartesian
     diagonal on represented coordinates; it does not own the tensor flip or
     the degree-two group-like equation.
   * Pinned Mathlib supplies the canonical tensor commutation equivalence and
     its pure-tensor, additive, and scalar compatibility laws.
   * Repository search found no existing D5 owner of the displayed group-like
     equation or its closure under chronological multiplication. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.TruncatedTensorHopf

open D5.S3.Observer.Chronology.TruncatedTensorSignature

noncomputable section

universe u v w

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- The canonical flip of a tensor square. -/
def tensorFlip : V ⊗[R] V →ₗ[R] V ⊗[R] V :=
  (TensorProduct.comm R V V).toLinearMap

@[simp]
theorem tensor_flip_tmul (left right : V) :
    tensorFlip (R := R) (V := V) (left ⊗ₜ[R] right) =
      right ⊗ₜ[R] left := by
  rfl

/-- Tensor flip is an involution. -/
theorem tensor_flip_involutive (tensor : V ⊗[R] V) :
    tensorFlip (R := R) (V := V)
        (tensorFlip (R := R) (V := V) tensor) = tensor := by
  exact (TensorProduct.comm R V V).symm_apply_apply tensor

/-- The doubled degree-two group-like equation. -/
def IsStepTwoGroupLike (signature : TensorSignature R V) : Prop :=
  signature.doubledDegreeTwo +
      tensorFlip signature.doubledDegreeTwo =
    (2 : R) • (signature.degreeOne ⊗ₜ[R] signature.degreeOne)

/-- The empty tensor signature is group-like. -/
theorem one_isStepTwoGroupLike :
    IsStepTwoGroupLike (1 : TensorSignature R V) := by
  simp [IsStepTwoGroupLike, tensorFlip]

/-- Every single-event tensor signature is group-like. -/
theorem event_tensor_signature_isStepTwoGroupLike (value : V) :
    IsStepTwoGroupLike (eventTensorSignature (R := R) value) := by
  simp [IsStepTwoGroupLike, eventTensorSignature, tensorFlip, two_smul]

/-- The degree-two group-like equation is preserved by Chen multiplication. -/
theorem isStepTwoGroupLike_mul
    {left right : TensorSignature R V}
    (hLeft : IsStepTwoGroupLike left)
    (hRight : IsStepTwoGroupLike right) :
    IsStepTwoGroupLike (left * right) := by
  rw [IsStepTwoGroupLike] at hLeft hRight ⊢
  change
    (left.doubledDegreeTwo +
          (2 : R) • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
          right.doubledDegreeTwo) +
        tensorFlip
          (left.doubledDegreeTwo +
            (2 : R) • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
            right.doubledDegreeTwo) =
      (2 : R) •
        ((left.degreeOne + right.degreeOne) ⊗ₜ[R]
          (left.degreeOne + right.degreeOne))
  simp only [map_add, LinearMap.map_smul, tensor_flip_tmul,
    add_tmul, tmul_add, smul_add]
  calc
    (left.doubledDegreeTwo +
          (2 : R) • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
          right.doubledDegreeTwo) +
        (tensorFlip left.doubledDegreeTwo +
          (2 : R) • (right.degreeOne ⊗ₜ[R] left.degreeOne) +
          tensorFlip right.doubledDegreeTwo) =
      (left.doubledDegreeTwo + tensorFlip left.doubledDegreeTwo) +
        (right.doubledDegreeTwo + tensorFlip right.doubledDegreeTwo) +
        (2 : R) • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
        (2 : R) • (right.degreeOne ⊗ₜ[R] left.degreeOne) := by
          abel
    _ =
      (2 : R) • (left.degreeOne ⊗ₜ[R] left.degreeOne) +
        (2 : R) • (right.degreeOne ⊗ₜ[R] right.degreeOne) +
        (2 : R) • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
        (2 : R) • (right.degreeOne ⊗ₜ[R] left.degreeOne) := by
          rw [hLeft, hRight]
    _ =
      (2 : R) •
        (left.degreeOne ⊗ₜ[R] left.degreeOne +
          left.degreeOne ⊗ₜ[R] right.degreeOne +
          (right.degreeOne ⊗ₜ[R] left.degreeOne +
            right.degreeOne ⊗ₜ[R] right.degreeOne)) := by
          simp only [smul_add]
          abel

/-- Every finite chronological tensor word is group-like. -/
theorem chronological_tensor_signature_isStepTwoGroupLike
    {Event : Type w} (observe : Event → V) (events : List Event) :
    IsStepTwoGroupLike
      (chronologicalTensorSignature (R := R) observe events) := by
  induction events with
  | nil =>
      exact one_isStepTwoGroupLike
  | cons event events inductionHypothesis =>
      rw [chronological_tensor_signature_cons]
      exact isStepTwoGroupLike_mul
        (event_tensor_signature_isStepTwoGroupLike (observe event))
        inductionHypothesis

/-- The symmetric part of doubled degree two is fixed by degree one for every
chronological word. -/
theorem chronological_tensor_signature_symmetric_part
    {Event : Type w} (observe : Event → V) (events : List Event) :
    let signature := chronologicalTensorSignature (R := R) observe events
    signature.doubledDegreeTwo + tensorFlip signature.doubledDegreeTwo =
      (2 : R) • (signature.degreeOne ⊗ₜ[R] signature.degreeOne) := by
  exact chronological_tensor_signature_isStepTwoGroupLike observe events

example :
    IsStepTwoGroupLike
      (eventTensorSignature (R := ℤ) (V := ℤ) 1) := by
  exact event_tensor_signature_isStepTwoGroupLike 1

#print axioms tensor_flip_involutive
#print axioms event_tensor_signature_isStepTwoGroupLike
#print axioms isStepTwoGroupLike_mul
#print axioms chronological_tensor_signature_isStepTwoGroupLike
#print axioms chronological_tensor_signature_symmetric_part

end

end D5.S3.Observer.Chronology.TruncatedTensorHopf
