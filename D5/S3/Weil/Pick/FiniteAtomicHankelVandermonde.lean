/- GID: D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/FiniteAtomicHankelVandermonde
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor finite atomic Hankel moment matrices and their shifted pencil through a shared Vandermonde feature matrix. -/

import Mathlib.Tactic

/-!
# Finite atomic Hankel and Vandermonde factorization

A finite atomic moment sequence has the form

`mu k = sum_a weight a * node a ^ k`.

Its Hankel matrix factors as `V W Vᵀ`, while the once-shifted Hankel matrix uses
the same Vandermonde matrix and the diagonal weights `weight a * node a`.
Consequently, their pencil has diagonal weights
`weight a * (node a - lambda)`.

These are exact finite algebraic identities. No distinctness, invertibility,
rank equality, inertia equality, or infinite contour limit is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset
open scoped BigOperators

namespace D5.S3.Weil.Pick.FiniteAtomicHankelVandermonde

variable {Atom : Type*} [Fintype Atom] [DecidableEq Atom]

/-- Moment sequence of a finite complex atomic family. -/
def atomicMoment
    (weight node : Atom → ℂ) (degree : ℕ) : ℂ :=
  ∑ a, weight a * node a ^ degree

/-- Rectangular Vandermonde feature matrix through a chosen truncation order. -/
def vandermondeFeatureMatrix
    (node : Atom → ℂ) (order : ℕ) : Matrix (Fin order) Atom ℂ :=
  fun i a => node a ^ (i : ℕ)

/-- Diagonal atomic weight matrix. -/
def atomicWeightMatrix
    (weight : Atom → ℂ) : Matrix Atom Atom ℂ :=
  Matrix.diagonal weight

/-- Diagonal weight matrix after one moment shift. -/
def shiftedAtomicWeightMatrix
    (weight node : Atom → ℂ) : Matrix Atom Atom ℂ :=
  Matrix.diagonal (fun a => weight a * node a)

/-- Diagonal weight matrix of the shifted-minus-unshifted moment pencil. -/
def atomicPencilWeightMatrix
    (weight node : Atom → ℂ) (lambda : ℂ) : Matrix Atom Atom ℂ :=
  Matrix.diagonal (fun a => weight a * (node a - lambda))

/-- Finite Hankel matrix `H_ij = mu_(i+j)`. -/
def hankelMomentMatrix
    (weight node : Atom → ℂ) (order : ℕ) :
    Matrix (Fin order) (Fin order) ℂ :=
  fun i j => atomicMoment weight node ((i : ℕ) + (j : ℕ))

/-- Once-shifted Hankel matrix `H⁺_ij = mu_(i+j+1)`. -/
def shiftedHankelMomentMatrix
    (weight node : Atom → ℂ) (order : ℕ) :
    Matrix (Fin order) (Fin order) ℂ :=
  fun i j => atomicMoment weight node ((i : ℕ) + (j : ℕ) + 1)

/-- Entrywise finite atomic moment pencil. -/
def hankelMomentPencil
    (weight node : Atom → ℂ) (order : ℕ) (lambda : ℂ) :
    Matrix (Fin order) (Fin order) ℂ :=
  fun i j =>
    ∑ a, weight a * (node a - lambda) *
      node a ^ ((i : ℕ) + (j : ℕ))

/-- The unshifted finite Hankel matrix factors through the Vandermonde features. -/
theorem hankel_moment_matrix_factorization
    (weight node : Atom → ℂ) (order : ℕ) :
    hankelMomentMatrix weight node order =
      vandermondeFeatureMatrix node order *
        atomicWeightMatrix weight *
        Matrix.transpose (vandermondeFeatureMatrix node order) := by
  classical
  ext i j
  simp [hankelMomentMatrix, atomicMoment, vandermondeFeatureMatrix,
    atomicWeightMatrix, Matrix.mul_apply, pow_add,
    mul_comm, mul_left_comm, mul_assoc]

/-- The once-shifted Hankel matrix uses the same Vandermonde features and
multiplies each atomic weight by its node. -/
theorem shifted_hankel_moment_matrix_factorization
    (weight node : Atom → ℂ) (order : ℕ) :
    shiftedHankelMomentMatrix weight node order =
      vandermondeFeatureMatrix node order *
        shiftedAtomicWeightMatrix weight node *
        Matrix.transpose (vandermondeFeatureMatrix node order) := by
  classical
  ext i j
  simp [shiftedHankelMomentMatrix, atomicMoment,
    vandermondeFeatureMatrix, shiftedAtomicWeightMatrix,
    Matrix.mul_apply, pow_add, pow_succ,
    mul_comm, mul_left_comm, mul_assoc]

/-- The entrywise pencil is exactly shifted Hankel minus `lambda` times the
unshifted Hankel matrix. -/
theorem hankel_moment_pencil_eq_shifted_sub
    (weight node : Atom → ℂ) (order : ℕ) (lambda : ℂ) :
    hankelMomentPencil weight node order lambda =
      shiftedHankelMomentMatrix weight node order -
        lambda • hankelMomentMatrix weight node order := by
  classical
  ext i j
  change
    (∑ a, weight a * (node a - lambda) *
      node a ^ ((i : ℕ) + (j : ℕ))) =
      (∑ a, weight a * node a ^ ((i : ℕ) + (j : ℕ) + 1)) -
        lambda * (∑ a, weight a * node a ^ ((i : ℕ) + (j : ℕ)))
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [pow_succ]
  ring

/-- The whole Hankel pencil factors through one shifted diagonal weight matrix. -/
theorem hankel_moment_pencil_factorization
    (weight node : Atom → ℂ) (order : ℕ) (lambda : ℂ) :
    hankelMomentPencil weight node order lambda =
      vandermondeFeatureMatrix node order *
        atomicPencilWeightMatrix weight node lambda *
        Matrix.transpose (vandermondeFeatureMatrix node order) := by
  classical
  ext i j
  simp [hankelMomentPencil, vandermondeFeatureMatrix,
    atomicPencilWeightMatrix, Matrix.mul_apply, pow_add,
    mul_comm, mul_left_comm, mul_assoc]

#print axioms hankel_moment_matrix_factorization
#print axioms shifted_hankel_moment_matrix_factorization
#print axioms hankel_moment_pencil_eq_shifted_sub
#print axioms hankel_moment_pencil_factorization

end D5.S3.Weil.Pick.FiniteAtomicHankelVandermonde
