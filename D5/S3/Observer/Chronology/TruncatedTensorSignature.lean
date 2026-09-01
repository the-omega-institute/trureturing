/- GID: D5/S3/Observer/Chronology/TruncatedTensorSignature
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/TruncatedTensorSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Degree-two tensor signatures carry Chen multiplication and finite chronological word signatures. -/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Truncated tensor chronological signature

For a module `V` over a commutative ring `R`, a normalized signature truncated
at tensor degree two is represented by its degree-one component and twice its
degree-two component.  The doubled convention avoids division by two:

`(x, D) * (y, E) = (x + y, D + 2 • (x ⊗ y) + E)`.

A single event has signature `(v, v ⊗ v)`.  Folding these event signatures in
list order gives a finite chronological tensor signature and satisfies the
step-two Chen append identity.

This file constructs only the finite degree-two tensor carrier and its Chen
multiplication.  The group-like equation, primitive Magnus coordinate,
free-Lie interpretation, infinite tensor completion, analytic convergence,
and rough-path estimates are separate layers.
-/

/- Library-search audit trail (2026-09-01):
   * `StepTwoChronologicalSignature` stores both degrees in one possibly
     noncommutative ring.  It is a represented shadow and does not own the
     universal tensor-square carrier formalized here.
   * Repository searches for truncated tensor signatures, tensor Chen
     multiplication, and chronological tensor words found no existing D5
     owner.
   * Pinned Mathlib supplies `TensorProduct`, pure tensors, bilinearity, and
     the additive algebra used in the monoid proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.TruncatedTensorSignature

noncomputable section

universe u v w

/-- Degree one together with twice tensor degree two. -/
@[ext]
structure TensorSignature (R : Type u) (V : Type v)
    [CommRing R] [AddCommGroup V] [Module R V] where
  degreeOne : V
  doubledDegreeTwo : V ⊗[R] V

namespace TensorSignature

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Step-two Chen multiplication in doubled tensor coordinates. -/
def compose (left right : TensorSignature R V) : TensorSignature R V where
  degreeOne := left.degreeOne + right.degreeOne
  doubledDegreeTwo :=
    left.doubledDegreeTwo +
      (2 : R) • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
        right.doubledDegreeTwo

/-- The empty tensor signature. -/
def identity : TensorSignature R V where
  degreeOne := 0
  doubledDegreeTwo := 0

/-- Chen multiplication is associative and unital. -/
instance : Monoid (TensorSignature R V) where
  one := identity
  mul := compose
  one_mul signature := by
    ext <;> simp [identity, compose]
  mul_one signature := by
    ext <;> simp [identity, compose]
  mul_assoc left middle right := by
    ext
    · simp [compose, add_assoc]
    · simp only [compose, add_tmul, tmul_add, map_add, smul_add]
      abel

@[simp]
theorem degreeOne_one :
    (1 : TensorSignature R V).degreeOne = 0 := by
  rfl

@[simp]
theorem doubledDegreeTwo_one :
    (1 : TensorSignature R V).doubledDegreeTwo = 0 := by
  rfl

@[simp]
theorem degreeOne_mul (left right : TensorSignature R V) :
    (left * right).degreeOne = left.degreeOne + right.degreeOne := by
  rfl

@[simp]
theorem doubledDegreeTwo_mul (left right : TensorSignature R V) :
    (left * right).doubledDegreeTwo =
      left.doubledDegreeTwo +
        (2 : R) • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
          right.doubledDegreeTwo := by
  rfl

end TensorSignature

/-- The truncated tensor signature of one event. -/
def eventTensorSignature
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (value : V) : TensorSignature R V where
  degreeOne := value
  doubledDegreeTwo := value ⊗ₜ[R] value

/-- Fold event signatures from left to right in operational chronology. -/
def chronologicalTensorSignature
    {R : Type u} {V : Type v} {Event : Type w}
    [CommRing R] [AddCommGroup V] [Module R V]
    (observe : Event → V) : List Event → TensorSignature R V
  | [] => 1
  | event :: events =>
      eventTensorSignature (observe event) *
        chronologicalTensorSignature observe events

@[simp]
theorem chronological_tensor_signature_nil
    {R : Type u} {V : Type v} {Event : Type w}
    [CommRing R] [AddCommGroup V] [Module R V]
    (observe : Event → V) :
    chronologicalTensorSignature observe [] = 1 := by
  rfl

@[simp]
theorem chronological_tensor_signature_cons
    {R : Type u} {V : Type v} {Event : Type w}
    [CommRing R] [AddCommGroup V] [Module R V]
    (observe : Event → V) (event : Event) (events : List Event) :
    chronologicalTensorSignature observe (event :: events) =
      eventTensorSignature (observe event) *
        chronologicalTensorSignature observe events := by
  rfl

/-- The tensor signature of an appended word is the Chen product of the two
word signatures. -/
theorem chronological_tensor_signature_append
    {R : Type u} {V : Type v} {Event : Type w}
    [CommRing R] [AddCommGroup V] [Module R V]
    (observe : Event → V) (earlierWord laterWord : List Event) :
    chronologicalTensorSignature observe (earlierWord ++ laterWord) =
      chronologicalTensorSignature observe earlierWord *
        chronologicalTensorSignature observe laterWord := by
  induction earlierWord with
  | nil =>
      simp
  | cons event earlierWord inductionHypothesis =>
      simp only [List.cons_append, chronological_tensor_signature_cons,
        inductionHypothesis]
      rw [mul_assoc]

/-- Degree one is the ordinary sum of observed event values. -/
theorem chronological_tensor_signature_degree_one
    {R : Type u} {V : Type v} {Event : Type w}
    [CommRing R] [AddCommGroup V] [Module R V]
    (observe : Event → V) (events : List Event) :
    (chronologicalTensorSignature observe events).degreeOne =
      (events.map observe).sum := by
  induction events with
  | nil =>
      rfl
  | cons event events inductionHypothesis =>
      simp [chronologicalTensorSignature, inductionHypothesis]

/-- The two-event signature records the ordered cross tensor. -/
theorem chronological_tensor_signature_two_events
    {R : Type u} {V : Type v}
    [CommRing R] [AddCommGroup V] [Module R V]
    (first second : V) :
    chronologicalTensorSignature (fun value : V => value) [first, second] =
      ⟨first + second,
        first ⊗ₜ[R] first +
          (2 : R) • (first ⊗ₜ[R] second) +
            second ⊗ₜ[R] second⟩ := by
  ext <;> simp [chronologicalTensorSignature, eventTensorSignature,
    TensorSignature.compose]

example : TensorSignature ℤ ℤ :=
  eventTensorSignature 1

#print axioms chronological_tensor_signature_append
#print axioms chronological_tensor_signature_degree_one
#print axioms chronological_tensor_signature_two_events

end

end D5.S3.Observer.Chronology.TruncatedTensorSignature
