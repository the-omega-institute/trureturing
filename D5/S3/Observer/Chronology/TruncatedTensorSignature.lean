/- GID: D5/S3/Observer/Chronology/TruncatedTensorSignature
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/TruncatedTensorSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Universal degree-two tensor signatures obey Chen concatenation. -/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Truncated tensor signatures

A chronological signature through tensor degree two stores a degree-one
vector together with twice its degree-two tensor. The doubled convention
avoids division by two. Composition inserts twice the ordered tensor cross
term. This gives a monoid and the signature of a concatenated event word is
the product of the two word signatures.

Unlike the existing ring-valued step-two shadow, the degree-two coordinate
here lives in the genuine tensor square `V ⊗[R] V`. No multiplication or
operator representation is chosen. Later nodes may apply a representation to
this universal tensor object.

This file does not construct the full tensor algebra, a completed signature,
a shuffle product, a coalgebra, primitive elements, rough integration, or an
analytic Magnus series.
-/

/- Library-search audit trail (2026-09-01):
   * `StepTwoChronologicalSignature` owns the represented ring-valued shadow.
     Its degree-two coordinate already multiplies inside one ring, so it is not
     the universal tensor-square owner introduced here.
   * Pinned Mathlib supplies `TensorProduct`, `tmul_add`, `add_tmul`, and the
     additive module laws used to prove associativity.
   * Repository searches found no existing chronological Chen monoid whose
     degree-two coordinate is a genuine tensor square. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open TensorProduct

namespace D5.S3.Observer.Chronology.TruncatedTensorSignature

universe u v w

variable (R : Type u) (V : Type v)
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- Degree one together with twice degree two in the genuine tensor square. -/
@[ext]
structure TensorSignature where
  degreeOne : V
  doubledDegreeTwo : V ⊗[R] V

namespace TensorSignature

variable {R V}

/-- Chronological composition. Every event represented by `left` occurs
before every event represented by `right`. -/
def compose
    (left right : TensorSignature R V) : TensorSignature R V where
  degreeOne := left.degreeOne + right.degreeOne
  doubledDegreeTwo :=
    left.doubledDegreeTwo +
      2 • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
      right.doubledDegreeTwo

/-- The empty tensor signature. -/
def identity : TensorSignature R V where
  degreeOne := 0
  doubledDegreeTwo := 0

/-- Truncated tensor signatures form a chronological monoid. -/
instance : Monoid (TensorSignature R V) where
  one := identity
  mul := compose
  one_mul signature := by
    change compose identity signature = signature
    rcases signature with ⟨degreeOne, degreeTwo⟩
    ext <;> simp [identity, compose]
  mul_one signature := by
    change compose signature identity = signature
    rcases signature with ⟨degreeOne, degreeTwo⟩
    ext <;> simp [identity, compose]
  mul_assoc left middle right := by
    change compose (compose left middle) right =
      compose left (compose middle right)
    rcases left with ⟨x, X⟩
    rcases middle with ⟨y, Y⟩
    rcases right with ⟨z, Z⟩
    ext
    · simp [compose, add_assoc]
    · simp only [compose, TensorProduct.add_tmul,
        TensorProduct.tmul_add, nsmul_add]
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
theorem degreeOne_mul
    (left right : TensorSignature R V) :
    (left * right).degreeOne = left.degreeOne + right.degreeOne := by
  rfl

@[simp]
theorem doubledDegreeTwo_mul
    (left right : TensorSignature R V) :
    (left * right).doubledDegreeTwo =
      left.doubledDegreeTwo +
        2 • (left.degreeOne ⊗ₜ[R] right.degreeOne) +
        right.doubledDegreeTwo := by
  rfl

end TensorSignature

/-- The truncated tensor signature of one event. -/
def eventTensorSignature (value : V) : TensorSignature R V where
  degreeOne := value
  doubledDegreeTwo := value ⊗ₜ[R] value

/-- The truncated tensor signature of a chronological event word. -/
def chronologicalTensorSignature
    {Event : Type w} (observe : Event → V) :
    List Event → TensorSignature R V
  | [] => 1
  | event :: events =>
      eventTensorSignature R V (observe event) *
        chronologicalTensorSignature observe events

@[simp]
theorem chronological_tensor_signature_nil
    {Event : Type w} (observe : Event → V) :
    chronologicalTensorSignature R V observe [] = 1 := by
  rfl

@[simp]
theorem chronological_tensor_signature_cons
    {Event : Type w} (observe : Event → V)
    (event : Event) (events : List Event) :
    chronologicalTensorSignature R V observe (event :: events) =
      eventTensorSignature R V (observe event) *
        chronologicalTensorSignature R V observe events := by
  rfl

/-- Chen concatenation through tensor degree two. -/
theorem chronological_tensor_signature_append
    {Event : Type w} (observe : Event → V)
    (earlierWord laterWord : List Event) :
    chronologicalTensorSignature R V observe (earlierWord ++ laterWord) =
      chronologicalTensorSignature R V observe earlierWord *
        chronologicalTensorSignature R V observe laterWord := by
  induction earlierWord with
  | nil =>
      simp [chronologicalTensorSignature]
  | cons event earlierWord inductionHypothesis =>
      simp [chronologicalTensorSignature, inductionHypothesis, mul_assoc]

/-- Degree one is the ordinary sum of the observed event vectors. -/
theorem chronological_tensor_signature_degree_one
    {Event : Type w} (observe : Event → V) (events : List Event) :
    (chronologicalTensorSignature R V observe events).degreeOne =
      (events.map observe).sum := by
  induction events with
  | nil =>
      simp [chronologicalTensorSignature]
  | cons event events inductionHypothesis =>
      simp [chronologicalTensorSignature, eventTensorSignature,
        inductionHypothesis]

/-- The two-event tensor signature displays the ordered cross term explicitly. -/
theorem chronological_tensor_signature_two_events
    (x y : V) :
    chronologicalTensorSignature R V (fun value : V => value) [x, y] =
      { degreeOne := x + y
        doubledDegreeTwo :=
          (x ⊗ₜ[R] x) + 2 • (x ⊗ₜ[R] y) + (y ⊗ₜ[R] y) } := by
  ext <;>
    simp [chronologicalTensorSignature, eventTensorSignature]

example : TensorSignature ℤ ℤ :=
  eventTensorSignature ℤ ℤ 1

#print axioms chronological_tensor_signature_append
#print axioms chronological_tensor_signature_degree_one
#print axioms chronological_tensor_signature_two_events

end D5.S3.Observer.Chronology.TruncatedTensorSignature
