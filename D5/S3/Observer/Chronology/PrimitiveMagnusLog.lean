/- GID: D5/S3/Observer/Chronology/PrimitiveMagnusLog
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/PrimitiveMagnusLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Subtracting the tensor square of degree one extracts the primitive alternating Magnus coordinate. -/

import D5.S3.Observer.Chronology.TruncatedTensorHopf
import Mathlib.Tactic

/-!
# Primitive degree-two Magnus logarithm

For a doubled step-two tensor signature `(x,D)`, define the doubled logarithmic
coordinate

`L₂ = D - x ⊗ x`.

The Chen product sends this coordinate to the degree-two BCH law, whose cross
term is the tensor Lie bracket `x ⊗ y - y ⊗ x`.  A group-like signature has an
alternating logarithmic coordinate, and the logarithm of two consecutive
events is exactly their tensor bracket.

This is the primitive degree-two shadow of the logarithm of a group-like
tensor series.  No infinite logarithm, completed tensor algebra, convergence,
or identification of all primitive elements with a completed free Lie algebra
is claimed here.
-/

/- Library-search audit trail (2026-09-01):
   * `TruncatedTensorSignature` owns the doubled Chen coordinates.
   * `TruncatedTensorHopf` owns tensor flip and the finite group-like equation.
   * `StepTwoChronologicalSignature` owns the represented ring-valued BCH
     coordinate, not the universal tensor-valued primitive coordinate below.
   * Repository search found no D5 owner of this tensor logarithm, its skew
     characterization, or its word-level BCH identity.
   * Pinned Mathlib supplies tensor bilinearity and additive normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.PrimitiveMagnusLog

open D5.S3.Observer.Chronology.TruncatedTensorSignature
open D5.S3.Observer.Chronology.TruncatedTensorHopf

noncomputable section

universe u v w

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- The universal doubled degree-two tensor bracket. -/
def tensorLieBracket (left right : V) : V ⊗[R] V :=
  left ⊗ₜ[R] right - right ⊗ₜ[R] left

/-- The doubled primitive degree-two coordinate. -/
def doubledPrimitiveMagnus (signature : TensorSignature R V) : V ⊗[R] V :=
  signature.doubledDegreeTwo -
    signature.degreeOne ⊗ₜ[R] signature.degreeOne

/-- A degree-two tensor is primitive in the alternating finite shadow when
its tensor flip is its additive inverse. -/
def IsAlternatingTensor (tensor : V ⊗[R] V) : Prop :=
  tensorFlip tensor = -tensor

/-- The tensor bracket reverses sign when its inputs are exchanged. -/
theorem tensor_lie_bracket_swap (left right : V) :
    tensorLieBracket right left = -tensorLieBracket left right := by
  simp [tensorLieBracket]

/-- The tensor bracket of one vector with itself vanishes. -/
theorem tensor_lie_bracket_self (value : V) :
    tensorLieBracket value value = 0 := by
  simp [tensorLieBracket]

/-- Tensor flip negates the universal tensor bracket. -/
theorem tensor_flip_lie_bracket (left right : V) :
    tensorFlip (tensorLieBracket left right) =
      -tensorLieBracket left right := by
  simp [tensorLieBracket, tensorFlip]

/-- The primitive coordinate obeys the doubled degree-two BCH law. -/
theorem doubled_primitive_magnus_mul
    (left right : TensorSignature R V) :
    doubledPrimitiveMagnus (left * right) =
      doubledPrimitiveMagnus left + doubledPrimitiveMagnus right +
        tensorLieBracket left.degreeOne right.degreeOne := by
  change
    (left.doubledDegreeTwo +
          (2 : R) • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
          right.doubledDegreeTwo) -
        ((left.degreeOne + right.degreeOne) ⊗ₜ[R]
          (left.degreeOne + right.degreeOne)) =
      (left.doubledDegreeTwo -
          left.degreeOne ⊗ₜ[R] left.degreeOne) +
        (right.doubledDegreeTwo -
          right.degreeOne ⊗ₜ[R] right.degreeOne) +
        (left.degreeOne ⊗ₜ[R] right.degreeOne -
          right.degreeOne ⊗ₜ[R] left.degreeOne)
  simp only [add_tmul, tmul_add, two_smul]
  abel

/-- A finite group-like signature has a primitive alternating logarithm. -/
theorem doubled_primitive_magnus_alternating
    {signature : TensorSignature R V}
    (hGroupLike : IsStepTwoGroupLike signature) :
    IsAlternatingTensor (doubledPrimitiveMagnus signature) := by
  unfold IsAlternatingTensor doubledPrimitiveMagnus
  rw [map_sub, tensor_flip_tmul]
  have hFlip :
      tensorFlip signature.doubledDegreeTwo =
        (2 : R) •
            (signature.degreeOne ⊗ₜ[R] signature.degreeOne) -
          signature.doubledDegreeTwo := by
    rw [IsStepTwoGroupLike] at hGroupLike
    apply eq_sub_of_add_eq
    simpa [add_comm] using hGroupLike
  rw [hFlip]
  simp only [two_smul]
  abel

/-- Two consecutive events have primitive logarithm equal to their tensor
Lie bracket. -/
theorem doubled_primitive_magnus_two_events
    (first second : V) :
    doubledPrimitiveMagnus
        (chronologicalTensorSignature
          (R := R) (fun value : V => value) [first, second]) =
      tensorLieBracket first second := by
  rw [chronological_tensor_signature_two_events]
  change
    (first ⊗ₜ[R] first +
          (2 : R) • (first ⊗ₜ[R] second) +
          second ⊗ₜ[R] second) -
        ((first + second) ⊗ₜ[R] (first + second)) =
      first ⊗ₜ[R] second - second ⊗ₜ[R] first
  simp only [add_tmul, tmul_add, two_smul]
  abel

/-- Reversing two events negates their primitive degree-two logarithm. -/
theorem doubled_primitive_magnus_two_events_swap
    (first second : V) :
    doubledPrimitiveMagnus
        (chronologicalTensorSignature
          (R := R) (fun value : V => value) [second, first]) =
      -doubledPrimitiveMagnus
        (chronologicalTensorSignature
          (R := R) (fun value : V => value) [first, second]) := by
  rw [doubled_primitive_magnus_two_events,
    doubled_primitive_magnus_two_events, tensor_lie_bracket_swap]

/-- Chen concatenation becomes the tensor BCH law for chronological words. -/
theorem doubled_primitive_magnus_append
    {Event : Type w} (observe : Event → V)
    (earlierWord laterWord : List Event) :
    doubledPrimitiveMagnus
        (chronologicalTensorSignature
          (R := R) observe (earlierWord ++ laterWord)) =
      doubledPrimitiveMagnus
          (chronologicalTensorSignature (R := R) observe earlierWord) +
        doubledPrimitiveMagnus
          (chronologicalTensorSignature (R := R) observe laterWord) +
        tensorLieBracket
          (chronologicalTensorSignature
            (R := R) observe earlierWord).degreeOne
          (chronologicalTensorSignature
            (R := R) observe laterWord).degreeOne := by
  rw [chronological_tensor_signature_append,
    doubled_primitive_magnus_mul]

/-- Every chronological word has an alternating primitive Magnus coordinate. -/
theorem chronological_primitive_magnus_alternating
    {Event : Type w} (observe : Event → V) (events : List Event) :
    IsAlternatingTensor
      (doubledPrimitiveMagnus
        (chronologicalTensorSignature (R := R) observe events)) := by
  exact doubled_primitive_magnus_alternating
    (chronological_tensor_signature_isStepTwoGroupLike observe events)

example :
    tensorLieBracket (R := ℤ) (1 : ℤ) 1 = 0 := by
  exact tensor_lie_bracket_self 1

#print axioms tensor_lie_bracket_swap
#print axioms tensor_flip_lie_bracket
#print axioms doubled_primitive_magnus_mul
#print axioms doubled_primitive_magnus_alternating
#print axioms doubled_primitive_magnus_two_events
#print axioms doubled_primitive_magnus_two_events_swap
#print axioms doubled_primitive_magnus_append
#print axioms chronological_primitive_magnus_alternating

end

end D5.S3.Observer.Chronology.PrimitiveMagnusLog
