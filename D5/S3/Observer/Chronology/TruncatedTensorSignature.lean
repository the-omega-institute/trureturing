/- GID: D5/S3/Observer/Chronology/TruncatedTensorSignature
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/TruncatedTensorSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Degree-one and doubled degree-two tensors form the universal step-two Chen signature with an alternating Magnus coordinate. -/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Truncated tensor signature

For a module `V` over a commutative ring `R`, the universal finite step-two
signature stores degree one in `V` and doubled degree two in `V ⊗[R] V`.
Chronological composition is

`(x,D) ⋆ (y,E) = (x+y, D + 2(x⊗y) + E)`.

A one-event signature is `(x,x⊗x)`. Iterating these signatures over a list
satisfies the exact Chen append identity. Subtracting `x⊗x` from doubled
degree two gives the doubled degree-two Magnus coordinate. Its product law
adds the alternating tensor commutator `x⊗y-y⊗x`.

This module supplies the tensor-valued carrier missing from the earlier
represented ring-valued step-two signature. It does not yet construct a
linear tensor bialgebra, a Mathlib `HopfAlgebra` instance, an infinite
signature, a completed tensor algebra, or analytic Magnus convergence.
-/

/- Library-search audit trail (2026-09-01):
   * `StepTwoChronologicalSignature` owns the represented ring-valued Chen and
     BCH formulas, where degree two has already been multiplied in an
     associative target ring.
   * Repository search found no owner whose degree-two coordinate remains in
     the genuine module tensor product.
   * Pinned Mathlib supplies `TensorProduct`, its flip equivalence, bilinearity
     lemmas, finite list sums, and additive normalization tactics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.TruncatedTensorSignature

universe u v w

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Degree one together with twice the degree-two tensor coordinate. -/
@[ext]
structure TensorSignature where
  degreeOne : V
  doubledDegreeTwo : V ⊗[R] V

/-- Add a tensor to itself without requiring division by two. -/
def twiceTensor (value : V ⊗[R] V) : V ⊗[R] V :=
  value + value

namespace TensorSignature

/-- Chronological Chen composition through degree two. The left signature is
the earlier word and the right signature is the later word. -/
def compose (left right : TensorSignature (R := R) (V := V)) :
    TensorSignature (R := R) (V := V) where
  degreeOne := left.degreeOne + right.degreeOne
  doubledDegreeTwo :=
    left.doubledDegreeTwo +
      twiceTensor (left.degreeOne ⊗ₜ[R] right.degreeOne) +
        right.doubledDegreeTwo

/-- Empty step-two tensor signature. -/
def identity : TensorSignature (R := R) (V := V) where
  degreeOne := 0
  doubledDegreeTwo := 0

/-- Truncated Chen composition is associative and unital. -/
instance : Monoid (TensorSignature (R := R) (V := V)) where
  one := identity
  mul := compose
  one_mul signature := by
    rcases signature with ⟨degreeOne, degreeTwo⟩
    ext <;> simp [identity, compose, twiceTensor]
  mul_one signature := by
    rcases signature with ⟨degreeOne, degreeTwo⟩
    ext <;> simp [identity, compose, twiceTensor]
  mul_assoc left middle right := by
    rcases left with ⟨x, X⟩
    rcases middle with ⟨y, Y⟩
    rcases right with ⟨z, Z⟩
    ext
    · simp [compose, add_assoc]
    · simp [compose, twiceTensor, add_tmul, tmul_add]
      abel

@[simp]
theorem degreeOne_one :
    (1 : TensorSignature (R := R) (V := V)).degreeOne = 0 := by
  rfl

@[simp]
theorem doubledDegreeTwo_one :
    (1 : TensorSignature (R := R) (V := V)).doubledDegreeTwo = 0 := by
  rfl

@[simp]
theorem degreeOne_mul
    (left right : TensorSignature (R := R) (V := V)) :
    (left * right).degreeOne = left.degreeOne + right.degreeOne := by
  rfl

@[simp]
theorem doubledDegreeTwo_mul
    (left right : TensorSignature (R := R) (V := V)) :
    (left * right).doubledDegreeTwo =
      left.doubledDegreeTwo +
        twiceTensor (left.degreeOne ⊗ₜ[R] right.degreeOne) +
          right.doubledDegreeTwo := by
  rfl

end TensorSignature

/-- The universal step-two signature of one observed event. -/
def eventTensorSignature (value : V) :
    TensorSignature (R := R) (V := V) where
  degreeOne := value
  doubledDegreeTwo := value ⊗ₜ[R] value

/-- Compose event signatures from left to right in operational chronology. -/
def chronologicalTensorSignature {Event : Type w}
    (observe : Event → V) :
    List Event → TensorSignature (R := R) (V := V)
  | [] => 1
  | event :: events =>
      eventTensorSignature (observe event) *
        chronologicalTensorSignature observe events

@[simp]
theorem chronological_tensor_signature_nil {Event : Type w}
    (observe : Event → V) :
    chronologicalTensorSignature (R := R) observe [] = 1 := by
  rfl

@[simp]
theorem chronological_tensor_signature_cons {Event : Type w}
    (observe : Event → V) (event : Event) (events : List Event) :
    chronologicalTensorSignature (R := R) observe (event :: events) =
      eventTensorSignature (R := R) (observe event) *
        chronologicalTensorSignature (R := R) observe events := by
  rfl

/-- The universal step-two signature obeys Chen concatenation. -/
theorem chronological_tensor_signature_append {Event : Type w}
    (observe : Event → V) (earlierWord laterWord : List Event) :
    chronologicalTensorSignature (R := R) observe
        (earlierWord ++ laterWord) =
      chronologicalTensorSignature (R := R) observe earlierWord *
        chronologicalTensorSignature (R := R) observe laterWord := by
  induction earlierWord with
  | nil => simp
  | cons event earlierWord inductionHypothesis =>
      simp [chronologicalTensorSignature, inductionHypothesis, mul_assoc]

/-- Degree one is the ordinary sum of the observed event values. -/
theorem chronological_tensor_signature_degree_one {Event : Type w}
    (observe : Event → V) (events : List Event) :
    (chronologicalTensorSignature (R := R) observe events).degreeOne =
      (events.map observe).sum := by
  induction events with
  | nil => rfl
  | cons event events inductionHypothesis =>
      simp [chronologicalTensorSignature, inductionHypothesis]

/-- Alternating degree-two tensor generated by two event values. -/
def tensorCommutator (left right : V) : V ⊗[R] V :=
  left ⊗ₜ[R] right - right ⊗ₜ[R] left

/-- The doubled degree-two logarithmic or Magnus coordinate. -/
def doubledTensorMagnus
    (signature : TensorSignature (R := R) (V := V)) : V ⊗[R] V :=
  signature.doubledDegreeTwo -
    signature.degreeOne ⊗ₜ[R] signature.degreeOne

/-- The tensor Magnus coordinate obeys the universal degree-two BCH law. -/
theorem doubled_tensor_magnus_mul
    (left right : TensorSignature (R := R) (V := V)) :
    doubledTensorMagnus (left * right) =
      doubledTensorMagnus left + doubledTensorMagnus right +
        tensorCommutator left.degreeOne right.degreeOne := by
  rcases left with ⟨x, X⟩
  rcases right with ⟨y, Y⟩
  simp [doubledTensorMagnus, TensorSignature.compose, twiceTensor,
    tensorCommutator, add_tmul, tmul_add]
  abel

/-- A one-event signature has no alternating degree-two memory. -/
theorem doubled_tensor_magnus_event_eq_zero (value : V) :
    doubledTensorMagnus (eventTensorSignature (R := R) value) = 0 := by
  simp [doubledTensorMagnus, eventTensorSignature]

/-- The two-event logarithmic coordinate is their tensor commutator. -/
theorem doubled_tensor_magnus_two_events (left right : V) :
    doubledTensorMagnus
        (eventTensorSignature (R := R) left *
          eventTensorSignature (R := R) right) =
      tensorCommutator left right := by
  rw [doubled_tensor_magnus_mul]
  simp [doubled_tensor_magnus_event_eq_zero]

/-- Reversing two events reverses the orientation of degree-two memory. -/
theorem doubled_tensor_magnus_two_events_swap (left right : V) :
    doubledTensorMagnus
        (eventTensorSignature (R := R) right *
          eventTensorSignature (R := R) left) =
      -doubledTensorMagnus
        (eventTensorSignature (R := R) left *
          eventTensorSignature (R := R) right) := by
  rw [doubled_tensor_magnus_two_events,
    doubled_tensor_magnus_two_events]
  simp [tensorCommutator]
  abel

/-- A tensor-symmetric event pair has zero degree-two chronological defect. -/
theorem doubled_tensor_magnus_two_events_eq_zero_of_tmul_commute
    (left right : V)
    (hCommute : left ⊗ₜ[R] right = right ⊗ₜ[R] left) :
    doubledTensorMagnus
        (eventTensorSignature (R := R) left *
          eventTensorSignature (R := R) right) = 0 := by
  rw [doubled_tensor_magnus_two_events]
  simp [tensorCommutator, hCommute]

example : TensorSignature (R := ℤ) (V := ℤ) :=
  eventTensorSignature (R := ℤ) 1

#print axioms chronological_tensor_signature_append
#print axioms chronological_tensor_signature_degree_one
#print axioms doubled_tensor_magnus_mul
#print axioms doubled_tensor_magnus_event_eq_zero
#print axioms doubled_tensor_magnus_two_events
#print axioms doubled_tensor_magnus_two_events_swap
#print axioms doubled_tensor_magnus_two_events_eq_zero_of_tmul_commute

end D5.S3.Observer.Chronology.TruncatedTensorSignature
