/- GID: D5/S3/Observer/Chronology/TruncatedTensorHopf
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/TruncatedTensorHopf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The degree-two group-like equation is multiplicative, and its logarithmic coordinate is exactly flip-primitive. -/

import D5.S3.Observer.Chronology.TruncatedTensorSignature
import Mathlib.Tactic

/-!
# Truncated tensor Hopf laws

The standard tensor Hopf algebra declares every degree-one generator
primitive. Through degree two, a normalized signature `(x,D)`, with `D` equal
to twice degree two, is group-like exactly when

`D + flip D = 2 (x ⊗ x)`.

The doubled logarithmic coordinate is `L = D - x ⊗ x`. The group-like equation
is equivalent to the primitive antisymmetry law `flip L = -L`. This module
proves that the group-like equation is preserved by Chen multiplication and
that every chronological tensor word satisfies it.

These are the exact degree-at-most-two component equations of the standard
tensor Hopf structure. The module deliberately does not present the cartesian
diagonal of a type as a coalgebra. It also does not yet instantiate Mathlib's
full `HopfAlgebra` hierarchy on a completed or untruncated tensor algebra.
-/

/- Library-search audit trail (2026-09-01):
   * `TruncatedTensorSignature` owns the universal tensor-valued Chen product
     and doubled Magnus coordinate.
   * Pinned Mathlib supplies the tensor flip linear equivalence and its pure
     tensor computation rule.
   * Pinned Mathlib has standard `HopfAlgebra`, `IsGroupLikeElem`, and primitive
     element APIs, but no tensor-algebra Hopf instance whose degree-two
     projection directly discharges the equations below.
   * Repository search found no existing owner of the doubled degree-two
     group-like equation or its equivalence with flip-primitivity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.TruncatedTensorHopf

open D5.S3.Observer.Chronology.TruncatedTensorSignature

universe u v w

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Flip the two tensor factors. -/
def tensorFlip (value : V ⊗[R] V) : V ⊗[R] V :=
  TensorProduct.comm R V V value

@[simp]
theorem tensor_flip_tmul (left right : V) :
    tensorFlip (R := R) (left ⊗ₜ[R] right) = right ⊗ₜ[R] left := by
  rfl

@[simp]
theorem tensor_flip_zero :
    tensorFlip (R := R) (0 : V ⊗[R] V) = 0 := by
  exact map_zero (TensorProduct.comm R V V)

@[simp]
theorem tensor_flip_add (left right : V ⊗[R] V) :
    tensorFlip (R := R) (left + right) =
      tensorFlip (R := R) left + tensorFlip (R := R) right := by
  exact map_add (TensorProduct.comm R V V) left right

@[simp]
theorem tensor_flip_sub (left right : V ⊗[R] V) :
    tensorFlip (R := R) (left - right) =
      tensorFlip (R := R) left - tensorFlip (R := R) right := by
  exact map_sub (TensorProduct.comm R V V) left right

@[simp]
theorem tensor_flip_neg (value : V ⊗[R] V) :
    tensorFlip (R := R) (-value) = -tensorFlip (R := R) value := by
  exact map_neg (TensorProduct.comm R V V) value

/-- The tensor flip is an involution. -/
theorem tensor_flip_involutive (value : V ⊗[R] V) :
    tensorFlip (R := R) (tensorFlip (R := R) value) = value := by
  induction value using TensorProduct.induction_on with
  | zero => simp
  | tmul left right => simp
  | add left right hLeft hRight => simp [hLeft, hRight]

/-- The exact doubled degree-two component equation for a normalized
step-two group-like tensor signature. -/
def IsStepTwoGroupLike
    (signature : TensorSignature (R := R) (V := V)) : Prop :=
  signature.doubledDegreeTwo +
      tensorFlip (R := R) signature.doubledDegreeTwo =
    twiceTensor (signature.degreeOne ⊗ₜ[R] signature.degreeOne)

/-- The exact degree-two primitive condition. -/
def IsStepTwoPrimitive (value : V ⊗[R] V) : Prop :=
  tensorFlip (R := R) value = -value

/-- The empty signature is group-like. -/
theorem one_isStepTwoGroupLike :
    IsStepTwoGroupLike
      (1 : TensorSignature (R := R) (V := V)) := by
  simp [IsStepTwoGroupLike, twiceTensor]

/-- Every one-event tensor signature is group-like through degree two. -/
theorem event_isStepTwoGroupLike (value : V) :
    IsStepTwoGroupLike (eventTensorSignature (R := R) value) := by
  simp [IsStepTwoGroupLike, eventTensorSignature, twiceTensor]

/-- The degree-two group-like equation is preserved by chronological Chen
multiplication. -/
theorem isStepTwoGroupLike_mul
    {left right : TensorSignature (R := R) (V := V)}
    (hLeft : IsStepTwoGroupLike left)
    (hRight : IsStepTwoGroupLike right) :
    IsStepTwoGroupLike (left * right) := by
  rcases left with ⟨x, X⟩
  rcases right with ⟨y, Y⟩
  change X + tensorFlip (R := R) X = twiceTensor (x ⊗ₜ[R] x) at hLeft
  change Y + tensorFlip (R := R) Y = twiceTensor (y ⊗ₜ[R] y) at hRight
  change
    (X + twiceTensor (x ⊗ₜ[R] y) + Y) +
        tensorFlip (R := R)
          (X + twiceTensor (x ⊗ₜ[R] y) + Y) =
      twiceTensor ((x + y) ⊗ₜ[R] (x + y))
  simp only [tensor_flip_add, tensor_flip_tmul]
  simp [twiceTensor, add_tmul, tmul_add]
  rw [hLeft, hRight]
  simp [twiceTensor, add_tmul, tmul_add]
  abel

/-- Every finite chronological tensor word is group-like through degree two. -/
theorem chronological_tensor_signature_isStepTwoGroupLike
    {Event : Type w} (observe : Event → V) (events : List Event) :
    IsStepTwoGroupLike
      (chronologicalTensorSignature (R := R) observe events) := by
  induction events with
  | nil => simpa using (one_isStepTwoGroupLike (R := R) (V := V))
  | cons event events inductionHypothesis =>
      rw [chronological_tensor_signature_cons]
      exact isStepTwoGroupLike_mul
        (event_isStepTwoGroupLike (R := R) (observe event))
        inductionHypothesis

/-- The group-like equation makes the doubled logarithmic coordinate
flip-primitive. -/
theorem groupLike_implies_magnus_primitive
    (signature : TensorSignature (R := R) (V := V))
    (hGroupLike : IsStepTwoGroupLike signature) :
    IsStepTwoPrimitive
      (doubledTensorMagnus signature) := by
  rcases signature with ⟨x, D⟩
  change D + tensorFlip (R := R) D = twiceTensor (x ⊗ₜ[R] x) at hGroupLike
  have hFlip :
      tensorFlip (R := R) D =
        twiceTensor (x ⊗ₜ[R] x) - D :=
    eq_sub_of_add_eq hGroupLike
  change
    tensorFlip (R := R) (D - x ⊗ₜ[R] x) =
      -(D - x ⊗ₜ[R] x)
  rw [tensor_flip_sub, tensor_flip_tmul, hFlip]
  simp [twiceTensor]
  abel

/-- Conversely, flip-primitivity of the logarithmic coordinate recovers the
step-two group-like equation. -/
theorem magnus_primitive_implies_groupLike
    (signature : TensorSignature (R := R) (V := V))
    (hPrimitive :
      IsStepTwoPrimitive (doubledTensorMagnus signature)) :
    IsStepTwoGroupLike signature := by
  rcases signature with ⟨x, D⟩
  change
    tensorFlip (R := R) (D - x ⊗ₜ[R] x) =
      -(D - x ⊗ₜ[R] x) at hPrimitive
  rw [tensor_flip_sub, tensor_flip_tmul] at hPrimitive
  change D + tensorFlip (R := R) D = twiceTensor (x ⊗ₜ[R] x)
  simp [twiceTensor] at hPrimitive ⊢
  abel

/-- Group-like step-two signatures are exactly those whose doubled logarithm
is flip-primitive. -/
theorem groupLike_iff_magnus_primitive
    (signature : TensorSignature (R := R) (V := V)) :
    IsStepTwoGroupLike signature ↔
      IsStepTwoPrimitive (doubledTensorMagnus signature) := by
  constructor
  · exact groupLike_implies_magnus_primitive signature
  · exact magnus_primitive_implies_groupLike signature

/-- The Magnus coordinate of every chronological word is primitive through
degree two. -/
theorem chronological_tensor_magnus_isStepTwoPrimitive
    {Event : Type w} (observe : Event → V) (events : List Event) :
    IsStepTwoPrimitive
      (doubledTensorMagnus
        (chronologicalTensorSignature (R := R) observe events)) := by
  exact groupLike_implies_magnus_primitive _
    (chronological_tensor_signature_isStepTwoGroupLike
      (R := R) observe events)

example :
    IsStepTwoGroupLike
      (eventTensorSignature (R := ℤ) (1 : ℤ)) := by
  exact event_isStepTwoGroupLike 1

#print axioms tensor_flip_involutive
#print axioms event_isStepTwoGroupLike
#print axioms isStepTwoGroupLike_mul
#print axioms chronological_tensor_signature_isStepTwoGroupLike
#print axioms groupLike_implies_magnus_primitive
#print axioms magnus_primitive_implies_groupLike
#print axioms groupLike_iff_magnus_primitive
#print axioms chronological_tensor_magnus_isStepTwoPrimitive

end D5.S3.Observer.Chronology.TruncatedTensorHopf
