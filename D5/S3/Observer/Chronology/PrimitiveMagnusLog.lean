/- GID: D5/S3/Observer/Chronology/PrimitiveMagnusLog
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/PrimitiveMagnusLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The degree-two logarithm of a group-like tensor signature is antisymmetric and obeys the truncated tensor BCH law. -/

import D5.S3.Observer.Chronology.TruncatedTensorHopf
import Mathlib.Tactic

/-!
# Primitive degree-two Magnus logarithm

For doubled degree two `D` and degree one `x`, the division-free logarithmic
coordinate is `D - x ⊗ x`. The degree-two group-like equation forces this
coordinate to be antisymmetric under exchange of tensor legs. Under Chen
multiplication it obeys the exact truncated BCH rule, with the tensor
commutator `x ⊗ y - y ⊗ x` as the cross term.

This is the primitive degree-two component of the finite tensor signature. No
completed logarithm, infinite Magnus series, or analytic convergence is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.PrimitiveMagnusLog

open D5.S3.Observer.Chronology.TruncatedTensorSignature
open D5.S3.Observer.Chronology.TruncatedTensorHopf

universe u v w

/-- The degree-two tensor commutator. -/
def tensorCommutator
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (x y : V) : TensorProduct R V V :=
  x ⊗ₜ[R] y - y ⊗ₜ[R] x

/-- Doubled degree-two coordinate of the truncated logarithm. -/
def doubledPrimitiveMagnus
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (signature : StepTwoTensorSignature R V) :
    TensorProduct R V V :=
  signature.doubledDegreeTwo -
    signature.degreeOne ⊗ₜ[R] signature.degreeOne

@[simp]
theorem tensorCommutator_self
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (x : V) : tensorCommutator (R := R) x x = 0 := by
  simp [tensorCommutator]

/-- Exchange of the two inputs reverses tensor-commutator orientation. -/
theorem tensorCommutator_swap
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (x y : V) :
    tensorCommutator (R := R) y x =
      -tensorCommutator (R := R) x y := by
  simp [tensorCommutator]

/-- The tensor commutator is antisymmetric under exchange of tensor legs. -/
theorem tensorFlip_tensorCommutator
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (x y : V) :
    tensorFlip R V (tensorCommutator (R := R) x y) =
      -tensorCommutator (R := R) x y := by
  simp [tensorCommutator, tensorFlip]

/-- The logarithmic degree-two coordinate of a group-like signature is
primitive, expressed at this truncation as tensor antisymmetry. -/
theorem doubledPrimitiveMagnus_antisymmetric
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    {signature : StepTwoTensorSignature R V}
    (hSignature : IsStepTwoGroupLike signature) :
    tensorFlip R V (doubledPrimitiveMagnus signature) =
      -doubledPrimitiveMagnus signature := by
  let D := signature.doubledDegreeTwo
  let x2 := signature.degreeOne ⊗ₜ[R] signature.degreeOne
  have hGroup : D + tensorFlip R V D = x2 + x2 := hSignature
  have hZero :
      doubledPrimitiveMagnus signature +
          tensorFlip R V (doubledPrimitiveMagnus signature) = 0 := by
    change
      (D - x2) + tensorFlip R V (D - x2) = 0
    rw [map_sub]
    change (D - x2) + (tensorFlip R V D - x2) = 0
    calc
      (D - x2) + (tensorFlip R V D - x2) =
          (D + tensorFlip R V D) - (x2 + x2) := by abel
      _ = 0 := by rw [hGroup]; simp
  exact eq_neg_of_add_eq_zero_left hZero

/-- The primitive logarithm obeys the degree-two tensor BCH identity. -/
theorem doubledPrimitiveMagnus_mul
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (earlier later : StepTwoTensorSignature R V) :
    doubledPrimitiveMagnus (earlier * later) =
      doubledPrimitiveMagnus earlier +
        doubledPrimitiveMagnus later +
        tensorCommutator (R := R)
          earlier.degreeOne later.degreeOne := by
  rcases earlier with ⟨x, X⟩
  rcases later with ⟨y, Y⟩
  simp [doubledPrimitiveMagnus, tensorCommutator,
    StepTwoTensorSignature.compose,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

/-- Chen concatenation becomes the tensor BCH rule after logarithm. -/
theorem doubledPrimitiveMagnus_append
    {R : Type u} {V : Type v} {Event : Type w}
    [CommRing R] [AddCommGroup V] [Module R V]
    (observe : Event → V) (earlierWord laterWord : List Event) :
    doubledPrimitiveMagnus
        (chronologicalTensorSignature (R := R) observe
          (earlierWord ++ laterWord)) =
      doubledPrimitiveMagnus
          (chronologicalTensorSignature (R := R) observe earlierWord) +
        doubledPrimitiveMagnus
          (chronologicalTensorSignature (R := R) observe laterWord) +
        tensorCommutator (R := R)
          (chronologicalTensorSignature
            (R := R) observe earlierWord).degreeOne
          (chronologicalTensorSignature
            (R := R) observe laterWord).degreeOne := by
  rw [chronological_tensor_signature_append,
    doubledPrimitiveMagnus_mul]

/-- The logarithm of a one-event signature has zero degree two. -/
@[simp]
theorem doubledPrimitiveMagnus_event
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (value : V) :
    doubledPrimitiveMagnus
      (eventTensorSignature (R := R) value) = 0 := by
  simp [doubledPrimitiveMagnus, eventTensorSignature]

/-- A two-event word has precisely the tensor commutator as its doubled
primitive Magnus coordinate. -/
theorem doubledPrimitiveMagnus_two_events
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (x y : V) :
    doubledPrimitiveMagnus
        (chronologicalTensorSignature (R := R) id [x, y]) =
      tensorCommutator (R := R) x y := by
  rw [show chronologicalTensorSignature (R := R) id [x, y] =
      eventTensorSignature (R := R) x * eventTensorSignature (R := R) y by
    rfl]
  rw [doubledPrimitiveMagnus_mul]
  simp

/-- Reversing two events reverses the primitive orientation. -/
theorem doubledPrimitiveMagnus_two_events_swap
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (x y : V) :
    doubledPrimitiveMagnus
        (chronologicalTensorSignature (R := R) id [y, x]) =
      -doubledPrimitiveMagnus
        (chronologicalTensorSignature (R := R) id [x, y]) := by
  rw [doubledPrimitiveMagnus_two_events,
    doubledPrimitiveMagnus_two_events, tensorCommutator_swap]

example :
    doubledPrimitiveMagnus
        (chronologicalTensorSignature (R := ℤ) id
          ([fun _ : Fin 2 => (0 : ℤ)] : List (Fin 2 → ℤ))) = 0 := by
  simp

#print axioms doubledPrimitiveMagnus_antisymmetric
#print axioms doubledPrimitiveMagnus_mul
#print axioms doubledPrimitiveMagnus_append
#print axioms doubledPrimitiveMagnus_two_events
#print axioms doubledPrimitiveMagnus_two_events_swap

end D5.S3.Observer.Chronology.PrimitiveMagnusLog
