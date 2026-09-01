/- GID: D5/S3/Observer/Chronology/TruncatedTensorHopf
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/TruncatedTensorHopf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Degree-two tensor signatures satisfy the exact group-like symmetry equation and are closed under Chen multiplication. -/

import D5.S3.Observer.Chronology.TruncatedTensorSignature
import Mathlib.Tactic

/-!
# Degree-two group-like tensor signatures

The standard tensor-Hopf coproduct makes degree-one generators primitive. At
truncation degree two, a normalized signature with degree-one coordinate `x`
and doubled degree-two coordinate `D` is group-like exactly when

`D + flip D = x ⊗ x + x ⊗ x`.

This module formalizes that equation in the actual tensor product, proves it
for one-event signatures, proves stability under Chen multiplication, and
therefore proves it for every finite chronological word. The declaration is
the degree-two group-like locus. It does not instantiate a quotient tensor
algebra or a completed Hopf algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.TruncatedTensorHopf

open D5.S3.Observer.Chronology.TruncatedTensorSignature

universe u v w

/-- Exchange the two degree-one tensor legs. -/
def tensorFlip
    (R : Type u) (V : Type v)
    [CommSemiring R] [AddCommMonoid V] [Module R V] :
    TensorProduct R V V ≃ₗ[R] TensorProduct R V V :=
  TensorProduct.comm R V V

@[simp]
theorem tensorFlip_tmul
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (x y : V) :
    tensorFlip R V (x ⊗ₜ[R] y) = y ⊗ₜ[R] x := by
  rfl

@[simp]
theorem tensorFlip_involutive
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (X : TensorProduct R V V) :
    tensorFlip R V (tensorFlip R V X) = X := by
  induction X using TensorProduct.induction_on with
  | zero => simp [tensorFlip]
  | tmul x y => rfl
  | add X Y hX hY => simp [hX, hY]

/-- The exact degree-two group-like equation in doubled coordinates. -/
def IsStepTwoGroupLike
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (signature : StepTwoTensorSignature R V) : Prop :=
  signature.doubledDegreeTwo +
      tensorFlip R V signature.doubledDegreeTwo =
    signature.degreeOne ⊗ₜ[R] signature.degreeOne +
      signature.degreeOne ⊗ₜ[R] signature.degreeOne

/-- The empty signature is group-like. -/
theorem one_isStepTwoGroupLike
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V] :
    IsStepTwoGroupLike (1 : StepTwoTensorSignature R V) := by
  simp [IsStepTwoGroupLike, tensorFlip]

/-- Every one-event truncated exponential is group-like. -/
theorem eventTensorSignature_isStepTwoGroupLike
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (value : V) :
    IsStepTwoGroupLike (eventTensorSignature (R := R) value) := by
  simp [IsStepTwoGroupLike, eventTensorSignature]

/-- The degree-two group-like locus is closed under Chen multiplication. -/
theorem IsStepTwoGroupLike.mul
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    {earlier later : StepTwoTensorSignature R V}
    (hEarlier : IsStepTwoGroupLike earlier)
    (hLater : IsStepTwoGroupLike later) :
    IsStepTwoGroupLike (earlier * later) := by
  rcases earlier with ⟨x, X⟩
  rcases later with ⟨y, Y⟩
  change
    (X + x ⊗ₜ[R] y + x ⊗ₜ[R] y + Y) +
        tensorFlip R V (X + x ⊗ₜ[R] y + x ⊗ₜ[R] y + Y) =
      (x + y) ⊗ₜ[R] (x + y) + (x + y) ⊗ₜ[R] (x + y)
  change X + tensorFlip R V X = x ⊗ₜ[R] x + x ⊗ₜ[R] x at hEarlier
  change Y + tensorFlip R V Y = y ⊗ₜ[R] y + y ⊗ₜ[R] y at hLater
  simp only [map_add, tensorFlip_tmul,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  rw [← hEarlier, ← hLater]
  abel

/-- Every finite chronological tensor signature is group-like at degree two. -/
theorem chronologicalTensorSignature_isStepTwoGroupLike
    {R : Type u} {V : Type v} {Event : Type w}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (observe : Event → V) (events : List Event) :
    IsStepTwoGroupLike
      (chronologicalTensorSignature (R := R) observe events) := by
  induction events with
  | nil =>
      exact one_isStepTwoGroupLike
  | cons event laterWord inductionHypothesis =>
      exact (eventTensorSignature_isStepTwoGroupLike
        (R := R) (observe event)).mul inductionHypothesis

/-- The symmetric part of doubled degree two is fixed by degree one. -/
theorem groupLike_symmetric_degree_two
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    {signature : StepTwoTensorSignature R V}
    (hSignature : IsStepTwoGroupLike signature) :
    signature.doubledDegreeTwo +
        tensorFlip R V signature.doubledDegreeTwo =
      signature.degreeOne ⊗ₜ[R] signature.degreeOne +
        signature.degreeOne ⊗ₜ[R] signature.degreeOne :=
  hSignature

example :
    IsStepTwoGroupLike
      (chronologicalTensorSignature (R := ℤ) id
        ([fun _ : Fin 2 => (0 : ℤ)] : List (Fin 2 → ℤ))) := by
  exact chronologicalTensorSignature_isStepTwoGroupLike _ _

#print axioms eventTensorSignature_isStepTwoGroupLike
#print axioms IsStepTwoGroupLike.mul
#print axioms chronologicalTensorSignature_isStepTwoGroupLike

end D5.S3.Observer.Chronology.TruncatedTensorHopf
