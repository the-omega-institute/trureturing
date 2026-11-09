/- GID: D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation
   generality: I
   mirror-B: D5/B/S3/QuadraticForms/FinchBalancedZerofreeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.claim; result=D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.result; claim=D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.claim
   digest: An explicit integer matrix refutes Finch's order-six zerofree conjecture. -/
/-
Steven Finch, arXiv:2605.03691v4, Conjecture 4, page 7:
"No 6×6 matrices exist that are tied to α=β=3."
The introduction, pages 1–2, requires integer unimodularity and no zero
entry in either the matrix or its inverse, with entrywise absolute maxima.

The preregistered public conventions in #25882 are retained verbatim under
Trureturing.OpenProblems.FinchUnimodularZerofree. The claim uses those public
symbols; the inverse and determinant-unit implications use Mathlib's owners
directly. Indices are zero-based. The source's signed-permutation
representatives preserve all these properties, so no representative selection
is needed.

admission_basis: open-problem-resolution (#25882; Refuted)
result — proof_shape: bind-only; escape_witness: none.
witness_mul — proof_shape: bind-only; consumer: result; escape_witness: none.
IntegerMatrix, maxAbsEntry, Unimodular, alpha, beta, Zerofree, claim,
witnessA, witnessB — proof_shape: bind-only (conventions, proposition and literal data).
Direct frozen dependencies: none, for every declaration; no D5 imports.
The finite certificates use normalization and Mathlib's inverse/unit lemmas.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Trureturing.OpenProblems.FinchUnimodularZerofree

/-- An n by n integer matrix, with indices 0 through n - 1. -/
abbrev IntegerMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

/-- The maximum absolute entry; the source uses this entrywise maximum. -/
def maxAbsEntry {n : ℕ} (M : IntegerMatrix n) : ℕ :=
  (Finset.univ : Finset (Fin n × Fin n)).sup (fun ij => (M ij.1 ij.2).natAbs)

/-- Over the integers, IsUnit det is det = 1 or det = -1. -/
abbrev Unimodular {n : ℕ} (M : IntegerMatrix n) : Prop := IsUnit M.det

/-- The source's alpha. -/
def alpha {n : ℕ} (M : IntegerMatrix n) : ℕ := maxAbsEntry M

/-- The source's beta, using Mathlib's nonsingular matrix inverse. -/
noncomputable def beta {n : ℕ} (M : IntegerMatrix n) : ℕ := maxAbsEntry M⁻¹

/-- Both the matrix and its inverse have no zero entry. -/
def Zerofree {n : ℕ} (M : IntegerMatrix n) : Prop :=
  (∀ i j : Fin n, M i j ≠ 0) ∧ (∀ i j : Fin n, M⁻¹ i j ≠ 0)

/-- Finch's Conjecture 4, with the introduction's predicates expanded. -/
def claim : Prop :=
  ∀ M : IntegerMatrix 6,
    Unimodular M →
    Zerofree M →
    alpha M = 3 →
    beta M = 3 →
    False

private def witnessA : Matrix (Fin 6) (Fin 6) ℤ := !![
  3, 2, 2, 2, 2, 2;
  2, 3, 2, 2, 2, 2;
  2, 2, 3, 2, 2, 2;
  2, 2, 2, 1, 2, 2;
  2, 2, 2, 2, 1, 2;
  2, 2, 2, 2, 2, 1]

private def witnessB : Matrix (Fin 6) (Fin 6) ℤ := !![
  -1, -2, -2, 2, 2, 2;
  -2, -1, -2, 2, 2, 2;
  -2, -2, -1, 2, 2, 2;
  2, 2, 2, -3, -2, -2;
  2, 2, 2, -2, -3, -2;
  2, 2, 2, -2, -2, -3]

private theorem witness_mul : witnessA * witnessB = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The displayed integral inverse gives a counterexample to Conjecture 4. -/
theorem result : ¬ claim := by
  intro h
  have hinv : witnessA⁻¹ = witnessB := Matrix.inv_eq_right_inv witness_mul
  apply h witnessA (Matrix.isUnit_det_of_right_inverse witness_mul)
  · constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [witnessA]
    · rw [hinv]
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [witnessB]
  · decide
  · change maxAbsEntry witnessA⁻¹ = 3
    rw [hinv]
    decide

end Trureturing.OpenProblems.FinchUnimodularZerofree
