/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyShiftedHankelTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every shifted finite Prony Hankel section factors through one Vandermonde observation map while time shift acts only on the diagonal modal weights. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Shifted finite Prony Hankel transport

The source Hankel factorization is strengthened from the unshifted section to
an arbitrary observation-time shift. For

`c_n = sum_j weight_j * node_j^n`,

the shifted section `H_shift(row, column) = c_(shift + row + column)` factors
through the same rectangular Vandermonde map at every shift. Only the hidden
diagonal modal weights change, by multiplication with `node_j^shift`.

This exact factorization is the finite algebraic bridge from Hankel moments to
matrix-pencil and Koopman transport. It does not assert spectral recovery from
noisy data, invertibility of a square section, or an infinite-delay limit.
-/

/- Library-search audit trail (2026-09-03):
   * Current-tree searches for shifted Prony Hankel factorization, Hankel modal
     transport, and a finite matrix-pencil bridge found no declaration on `dev`.
   * The open source atom supplies the unshifted Hankel matrix and factorization
     in formulas (1295.5)--(1295.6). This module proves the stronger finite shift
     family while reusing the existing `finitePronyMoment` owner.
   * Pinned Mathlib supplies matrix multiplication, diagonal matrices,
     transposition, `Matrix.mul_diagonal`, and finite-sum algebra. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport

open scoped BigOperators
open Matrix
open D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction

/-- Observation times on rows and hidden modes on columns. -/
def finitePronyVandermonde {m n : ℕ}
    (nodes : Fin m → ℂ) : Matrix (Fin n) (Fin m) ℂ :=
  fun time mode => nodes mode ^ (time : ℕ)

/-- Modal weights after `shift` applications of the diagonal hidden transport. -/
def finitePronyShiftedWeights {m : ℕ}
    (nodes weights : Fin m → ℂ) (shift : ℕ) : Fin m → ℂ :=
  fun mode => weights mode * nodes mode ^ shift

/-- The Hankel section beginning at the supplied time shift. -/
def finitePronyShiftedHankel {m n : ℕ}
    (nodes weights : Fin m → ℂ) (shift : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun row column =>
    finitePronyMoment nodes weights
      (shift + (row : ℕ) + (column : ℕ))

/-- Formula (1295.6), uniformly at every time shift: the observation map is
fixed and the elapsed time is carried only by the diagonal modal weights. -/
theorem finite_prony_shifted_hankel_factorization {m n : ℕ}
    (nodes weights : Fin m → ℂ) (shift : ℕ) :
    finitePronyShiftedHankel (n := n) nodes weights shift =
      finitePronyVandermonde (n := n) nodes *
        Matrix.diagonal (finitePronyShiftedWeights nodes weights shift) *
          (finitePronyVandermonde (n := n) nodes)ᵀ := by
  classical
  ext row column
  unfold finitePronyShiftedHankel finitePronyMoment
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro mode hMode
  rw [Matrix.mul_diagonal]
  simp only [finitePronyVandermonde, finitePronyShiftedWeights,
    transpose_apply]
  simp only [pow_add]
  ring

/-- The source unshifted Hankel factorization is the zero-shift specialization
of the transport family. -/
theorem finite_prony_hankel_factorization {m n : ℕ}
    (nodes weights : Fin m → ℂ) :
    finitePronyShiftedHankel (n := n) nodes weights 0 =
      finitePronyVandermonde (n := n) nodes *
        Matrix.diagonal weights *
          (finitePronyVandermonde (n := n) nodes)ᵀ := by
  simpa [finitePronyShiftedWeights] using
    (finite_prony_shifted_hankel_factorization
      (n := n) nodes weights 0)

/-- One further observation-time step multiplies each hidden modal weight by
its transport node. -/
theorem finite_prony_shifted_hankel_succ_transport {m n : ℕ}
    (nodes weights : Fin m → ℂ) (shift : ℕ) :
    finitePronyShiftedHankel (n := n) nodes weights (shift + 1) =
      finitePronyVandermonde (n := n) nodes *
        Matrix.diagonal
          (fun mode =>
            finitePronyShiftedWeights nodes weights shift mode * nodes mode) *
          (finitePronyVandermonde (n := n) nodes)ᵀ := by
  simpa [finitePronyShiftedWeights, pow_succ, mul_assoc] using
    (finite_prony_shifted_hankel_factorization
      (n := n) nodes weights (shift + 1))

/-- Modal time shifts compose additively and act multiplicatively on every
hidden fiber. -/
theorem finite_prony_shifted_weights_add {m : ℕ}
    (nodes weights : Fin m → ℂ) (first second : ℕ) (mode : Fin m) :
    finitePronyShiftedWeights nodes weights (first + second) mode =
      finitePronyShiftedWeights nodes weights first mode *
        nodes mode ^ second := by
  simp [finitePronyShiftedWeights, pow_add, mul_assoc]

/-- The exact shifted-Hankel transport package. -/
theorem finite_prony_shifted_hankel_transport_package {m n : ℕ}
    (nodes weights : Fin m → ℂ) :
    (∀ shift : ℕ,
      finitePronyShiftedHankel (n := n) nodes weights shift =
        finitePronyVandermonde (n := n) nodes *
          Matrix.diagonal (finitePronyShiftedWeights nodes weights shift) *
            (finitePronyVandermonde (n := n) nodes)ᵀ) ∧
    (∀ shift : ℕ,
      finitePronyShiftedHankel (n := n) nodes weights (shift + 1) =
        finitePronyVandermonde (n := n) nodes *
          Matrix.diagonal
            (fun mode =>
              finitePronyShiftedWeights nodes weights shift mode * nodes mode) *
            (finitePronyVandermonde (n := n) nodes)ᵀ) :=
  ⟨finite_prony_shifted_hankel_factorization nodes weights,
    finite_prony_shifted_hankel_succ_transport nodes weights⟩

-- A one-mode family gives an inhabited nonzero shifted-Hankel transport.
example (shift : ℕ) :
    finitePronyShiftedHankel
        (n := 1)
        (fun _ : Fin 1 => (2 : ℂ))
        (fun _ : Fin 1 => (3 : ℂ))
        shift =
      finitePronyVandermonde
          (n := 1) (fun _ : Fin 1 => (2 : ℂ)) *
        Matrix.diagonal
          (finitePronyShiftedWeights
            (fun _ : Fin 1 => (2 : ℂ))
            (fun _ : Fin 1 => (3 : ℂ))
            shift) *
        (finitePronyVandermonde
          (n := 1) (fun _ : Fin 1 => (2 : ℂ)))ᵀ :=
  finite_prony_shifted_hankel_factorization
    (n := 1)
    (fun _ : Fin 1 => (2 : ℂ))
    (fun _ : Fin 1 => (3 : ℂ))
    shift

#print axioms finite_prony_shifted_hankel_factorization
#print axioms finite_prony_hankel_factorization
#print axioms finite_prony_shifted_hankel_succ_transport
#print axioms finite_prony_shifted_weights_add
#print axioms finite_prony_shifted_hankel_transport_package

end D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport
