/- GID: D5/S3/Observer/Chronology/TruncatedTensorSignature
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/TruncatedTensorSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite event words carry a division-free degree-two tensor signature satisfying Chen concatenation. -/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Truncated tensor signatures

For a module `V` over a commutative semiring `R`, a finite step-two signature
stores degree one in `V` and twice degree two in `V ⊗[R] V`. The doubled
coordinate avoids division by two and composes by the ordered cross term

`D(xy) = D(x) + x₁ ⊗ y₁ + x₁ ⊗ y₁ + D(y)`.

The recursively defined signature of an event list satisfies the exact Chen
append identity. This is the finite algebraic signature layer. It does not
construct a completed tensor algebra, an infinite signature, a rough path, or
an analytic convergence theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.TruncatedTensorSignature

universe u v w

/-- Degree one together with the doubled degree-two tensor coordinate. -/
@[ext]
structure StepTwoTensorSignature
    (R : Type u) (V : Type v)
    [CommSemiring R] [AddCommMonoid V] [Module R V] where
  degreeOne : V
  doubledDegreeTwo : TensorProduct R V V

namespace StepTwoTensorSignature

variable {R : Type u} {V : Type v}
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- Chronological composition with the ordered cross tensor written twice. -/
def compose
    (earlier later : StepTwoTensorSignature R V) :
    StepTwoTensorSignature R V where
  degreeOne := earlier.degreeOne + later.degreeOne
  doubledDegreeTwo :=
    earlier.doubledDegreeTwo +
      earlier.degreeOne ⊗ₜ[R] later.degreeOne +
      earlier.degreeOne ⊗ₜ[R] later.degreeOne +
      later.doubledDegreeTwo

/-- Empty step-two signature. -/
def identity : StepTwoTensorSignature R V where
  degreeOne := 0
  doubledDegreeTwo := 0

/-- The chronological composition law is associative and unital. -/
instance : Monoid (StepTwoTensorSignature R V) where
  one := identity
  mul := compose
  one_mul signature := by
    rcases signature with ⟨x, X⟩
    ext <;> simp [identity, compose]
  mul_one signature := by
    rcases signature with ⟨x, X⟩
    ext <;> simp [identity, compose]
  mul_assoc first second third := by
    rcases first with ⟨x, X⟩
    rcases second with ⟨y, Y⟩
    rcases third with ⟨z, Z⟩
    ext
    · simp [compose, add_assoc]
    · simp [compose, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel

@[simp]
theorem degreeOne_one :
    (1 : StepTwoTensorSignature R V).degreeOne = 0 := by
  rfl

@[simp]
theorem doubledDegreeTwo_one :
    (1 : StepTwoTensorSignature R V).doubledDegreeTwo = 0 := by
  rfl

@[simp]
theorem degreeOne_mul
    (earlier later : StepTwoTensorSignature R V) :
    (earlier * later).degreeOne =
      earlier.degreeOne + later.degreeOne := by
  rfl

@[simp]
theorem doubledDegreeTwo_mul
    (earlier later : StepTwoTensorSignature R V) :
    (earlier * later).doubledDegreeTwo =
      earlier.doubledDegreeTwo +
        earlier.degreeOne ⊗ₜ[R] later.degreeOne +
        earlier.degreeOne ⊗ₜ[R] later.degreeOne +
        later.doubledDegreeTwo := by
  rfl

end StepTwoTensorSignature

/-- The division-free step-two signature of one event value. -/
def eventTensorSignature
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (value : V) : StepTwoTensorSignature R V where
  degreeOne := value
  doubledDegreeTwo := value ⊗ₜ[R] value

/-- The step-two tensor signature of a finite operational chronology. -/
def chronologicalTensorSignature
    {R : Type u} {V : Type v} {Event : Type w}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (observe : Event → V) : List Event → StepTwoTensorSignature R V
  | [] => 1
  | event :: laterWord =>
      eventTensorSignature (observe event) *
        chronologicalTensorSignature observe laterWord

@[simp]
theorem chronological_tensor_signature_nil
    {R : Type u} {V : Type v} {Event : Type w}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (observe : Event → V) :
    chronologicalTensorSignature observe [] = 1 := by
  rfl

@[simp]
theorem chronological_tensor_signature_cons
    {R : Type u} {V : Type v} {Event : Type w}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (observe : Event → V) (event : Event) (laterWord : List Event) :
    chronologicalTensorSignature observe (event :: laterWord) =
      eventTensorSignature (observe event) *
        chronologicalTensorSignature observe laterWord := by
  rfl

/-- Chen concatenation for finite step-two tensor signatures. -/
theorem chronological_tensor_signature_append
    {R : Type u} {V : Type v} {Event : Type w}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (observe : Event → V) (earlierWord laterWord : List Event) :
    chronologicalTensorSignature observe (earlierWord ++ laterWord) =
      chronologicalTensorSignature observe earlierWord *
        chronologicalTensorSignature observe laterWord := by
  induction earlierWord with
  | nil =>
      simp
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, chronological_tensor_signature_cons]
      rw [inductionHypothesis, mul_assoc]

/-- Degree one is the ordinary sum of event values. -/
theorem chronological_tensor_signature_degree_one
    {R : Type u} {V : Type v} {Event : Type w}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (observe : Event → V) (events : List Event) :
    (chronologicalTensorSignature observe events).degreeOne =
      (events.map observe).sum := by
  induction events with
  | nil => simp
  | cons event rest inductionHypothesis =>
      simp [chronologicalTensorSignature, eventTensorSignature,
        inductionHypothesis]

/-- A two-event word exposes the ordered cross tensor explicitly. -/
theorem chronological_tensor_signature_two_events
    {R : Type u} {V : Type v}
    [CommSemiring R] [AddCommMonoid V] [Module R V]
    (x y : V) :
    chronologicalTensorSignature (R := R) id [x, y] =
      { degreeOne := x + y
        doubledDegreeTwo :=
          x ⊗ₜ[R] x + x ⊗ₜ[R] y +
            x ⊗ₜ[R] y + y ⊗ₜ[R] y } := by
  ext <;> simp [chronologicalTensorSignature, eventTensorSignature,
    StepTwoTensorSignature.compose, StepTwoTensorSignature.identity]

example : StepTwoTensorSignature ℤ (Fin 2 → ℤ) :=
  eventTensorSignature (fun _ => 0)

#print axioms chronological_tensor_signature_append
#print axioms chronological_tensor_signature_degree_one
#print axioms chronological_tensor_signature_two_events

end D5.S3.Observer.Chronology.TruncatedTensorSignature
