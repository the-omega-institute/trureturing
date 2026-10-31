/- GID: D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness
   generality: I
   mirror-B: D5/B/S3/HilbertOperators/ReversibleFourByFourNonuniqueness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.claim; result=D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.result; claim=D5/S3/HilbertOperators/ReversibleFourByFourNonuniqueness.claim
   digest: Weighted anticommuting matrices refute unitary uniqueness of reversible algebras. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The nonunital matrix-algebra reading of Blecher, arXiv:2509.17673v2,
Example 5.2 and its unitary-uniqueness conjecture; preregistration #24898. -/

set_option autoImplicit false

noncomputable section
namespace D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness

open scoped Matrix.Norms.L2Operator

/-- Multiplicative closure of a complex matrix subspace; no unit is required. -/
def IsMatrixAlgebra (b : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) : Prop :=
  ∀ x ∈ b, ∀ y ∈ b, x * y ∈ b

/-- Two elements of the algebra fail to commute. -/
def IsNoncommutative (b : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) : Prop :=
  ∃ x ∈ b, ∃ y ∈ b, x * y ≠ y * x

/-- Block assembly, with the scoped `Matrix.instL2OpNormedAddCommGroup` norm. -/
def blockMatrix {n k : ℕ} (x : Fin n → Fin n → Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ :=
  Matrix.of fun p q => x p.1 q.1 p.2 q.2

/-- A completely isometric representation with reversed multiplication.
All block norms use the scoped `Matrix.instL2OpNormedAddCommGroup` instance. -/
def IsReversible (b : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    ∃ ρ : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ,
      (∀ x ∈ b, ∀ y ∈ b, ρ (y * x) = ρ x * ρ y) ∧
      ∀ n (x : Fin n → Fin n → Matrix (Fin 4) (Fin 4) ℂ),
        (∀ i j, x i j ∈ b) →
        ‖blockMatrix (fun i j => ρ (x i j))‖ = ‖blockMatrix x‖

/-- The source CAR example, using zero-based indices for its matrix units. -/
def carAlgebra : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  let u : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 2 1 + Matrix.single 1 3 1
  let v : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 1 1 - Matrix.single 2 3 1
  Submodule.span ℂ {u, v, u * v}

/-- Unitary conjugation identifies the two subspaces. -/
def UnitarilyEquivalent (b c : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ)) : Prop :=
  ∃ q : Matrix.unitaryGroup (Fin 4) ℂ,
    ∀ x, x ∈ b ↔ star (q : Matrix (Fin 4) (Fin 4) ℂ) * x * q ∈ c

/-- Blecher's unitary-uniqueness conjecture under the preregistered formal reading. -/
def claim : Prop :=
  ∀ b : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ),
    IsMatrixAlgebra b → IsNoncommutative b → IsReversible b →
      UnitarilyEquivalent b carAlgebra

private def form (t a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, t * b, t * a, c; 0, 0, 0, a; 0, 0, 0, -b; 0, 0, 0, 0]

private def witness : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  Submodule.span ℂ {form 2 1 0 0, form 2 0 1 0, form 2 0 0 1}

private lemma form_linear (t a b c : ℂ) :
    a • form t 1 0 0 + b • form t 0 1 0 + c • form t 0 0 1 = form t a b c := by
  sorry

private lemma witness_coordinates (x : Matrix (Fin 4) (Fin 4) ℂ) :
    x ∈ witness ↔ ∃ a b c : ℂ, form 2 a b c = x := by
  sorry

private lemma car_coordinates (x : Matrix (Fin 4) (Fin 4) ℂ) :
    x ∈ carAlgebra ↔ ∃ a b c : ℂ, form 1 a b c = x := by
  sorry

private lemma form_product (t a b c d e f : ℂ) :
    form t a b c * form t d e f = form t 0 0 (t * (b * d - a * e)) := by
  sorry

private lemma witness_algebra : IsMatrixAlgebra witness := by
  sorry

private lemma witness_anticommutes (x : Matrix (Fin 4) (Fin 4) ℂ) (hx : x ∈ witness)
    (y : Matrix (Fin 4) (Fin 4) ℂ) (hy : y ∈ witness) : x * y = -(y * x) := by
  sorry

private lemma witness_noncommutative : IsNoncommutative witness := by
  sorry

private lemma witness_reversible : IsReversible witness := by
  sorry

private def conjugate (q : Matrix.unitaryGroup (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ ≃⋆ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix (Fin 4) (Fin 4) ℂ) (star q)

private lemma conjugate_trace (q : Matrix.unitaryGroup (Fin 4) ℂ)
    (x : Matrix (Fin 4) (Fin 4) ℂ) : Matrix.trace (conjugate q x) = Matrix.trace x := by
  sorry

private def delta (x : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  2 * Matrix.trace ((x * star x) ^ 2) - Matrix.trace (x * star x) ^ 2

private lemma delta_conjugate (q : Matrix.unitaryGroup (Fin 4) ℂ)
    (x : Matrix (Fin 4) (Fin 4) ℂ) : delta (conjugate q x) = delta x := by
  sorry

private lemma car_delta (a b : ℂ) : delta (form 1 a b 0) = 0 := by
  sorry

private lemma witness_delta : delta (form 2 1 0 0) = 9 := by
  sorry

private lemma conjugate_product_line (q : Matrix.unitaryGroup (Fin 4) ℂ)
    (h : ∀ x ∈ witness, conjugate q x ∈ carAlgebra) :
    ∃ t : ℂ, t ≠ 0 ∧ conjugate q (form 2 0 0 1) = t • form 1 0 0 1 := by
  sorry

private lemma conjugate_complement (q : Matrix.unitaryGroup (Fin 4) ℂ)
    (h : ∀ x ∈ witness, conjugate q x ∈ carAlgebra) :
    ∃ a b : ℂ, conjugate q (form 2 1 0 0) = form 1 a b 0 := by
  sorry

private lemma witness_not_equivalent : ¬ UnitarilyEquivalent witness carAlgebra := by
  sorry

/-- A second noncommutative reversible matrix algebra refutes unitary uniqueness. -/
theorem result : ¬ claim := by
  intro h
  exact witness_not_equivalent
    (h witness witness_algebra witness_noncommutative witness_reversible)

end D5.S3.HilbertOperators.ReversibleFourByFourNonuniqueness
