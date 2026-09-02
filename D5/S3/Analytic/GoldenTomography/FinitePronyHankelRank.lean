/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyHankelRank
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyHankelRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct Prony nodes with nonzero modal weights make every sufficiently long finite Hankel section have rank equal to the mode count. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport
import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact finite Prony Hankel rank

The shifted-Hankel factorization gives an upper rank bound by the number of
hidden modes. At zero shift, the leading square block factors through a square
Vandermonde matrix, a nonzero diagonal weight matrix, and its transpose.
Distinct nodes and nonzero weights make that block nonsingular, giving the
matching lower bound.

Thus every section with at least as many rows as active modes has rank exactly
the mode count. This is formula (1295.7) and the finite state-dimension bridge
used by Prony structures, matrix pencils, and minimal linear realizations.

No quantitative singular-value lower bound or noisy rank-selection theorem is
asserted.
-/

/- Library-search audit trail (2026-09-03):
   * Current-tree searches for exact Prony Hankel rank and finite exponential
     moment rank found no declaration on `dev`.
   * `FiniteVandermondeTomography` already owns the determinant nonvanishing
     theorem for injective nodes. `FinitePronyShiftedHankelTransport` owns the
     Hankel factorization. Both are reused rather than reproved.
   * Pinned Mathlib supplies determinant multiplicativity, determinant of a
     diagonal matrix, rank of a nonsingular square matrix, submatrix rank
     monotonicity, and rank bounds by matrix width. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePronyHankelRank

open Matrix
open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
open D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport

/-- A square Prony observation matrix is the transpose of Mathlib's canonical
Vandermonde matrix. -/
theorem square_finitePronyVandermonde_eq_transpose {m : ℕ}
    (nodes : Fin m → ℂ) :
    finitePronyVandermonde (n := m) nodes =
      (Matrix.vandermonde nodes)ᵀ := by
  rfl

/-- Embed the first `m` observation indices into any longer section. -/
def finInitialEmbedding {m n : ℕ} (hmn : m ≤ n) : Fin m → Fin n :=
  fun index => ⟨index, lt_of_lt_of_le index.isLt hmn⟩

/-- The leading `m × m` block of a longer zero-shift Hankel section is the
matching square section. -/
theorem finite_prony_hankel_initial_submatrix {m n : ℕ}
    (hmn : m ≤ n) (nodes weights : Fin m → ℂ) :
    (finitePronyShiftedHankel (n := n) nodes weights 0).submatrix
        (finInitialEmbedding hmn) (finInitialEmbedding hmn) =
      finitePronyShiftedHankel (n := m) nodes weights 0 := by
  rfl

/-- Formula (1295.7): distinct nodes and nonzero weights make every finite
Hankel section with at least as many rows as modes have rank exactly equal to
the mode count. -/
theorem finite_prony_hankel_rank {m n : ℕ}
    (hmn : m ≤ n) {nodes weights : Fin m → ℂ}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    Matrix.rank (finitePronyShiftedHankel (n := n) nodes weights 0) = m := by
  classical
  let V : Matrix (Fin m) (Fin m) ℂ :=
    finitePronyVandermonde (n := m) nodes
  let D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal weights
  have hDetV : Matrix.det V ≠ 0 := by
    rw [V, square_finitePronyVandermonde_eq_transpose,
      Matrix.det_transpose]
    exact vandermonde_det_ne_zero_of_injective hNodes
  have hDetD : Matrix.det D ≠ 0 := by
    rw [D, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun mode _ => hWeights mode
  have hSquareFactor :
      finitePronyShiftedHankel (n := m) nodes weights 0 =
        V * D * Vᵀ := by
    simpa [V, D] using
      finite_prony_hankel_factorization (n := m) nodes weights
  have hDetSquare :
      Matrix.det
          (finitePronyShiftedHankel (n := m) nodes weights 0) ≠ 0 := by
    rw [hSquareFactor, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hDetV hDetD) hDetV
  have hLower :
      m ≤ Matrix.rank
        (finitePronyShiftedHankel (n := n) nodes weights 0) := by
    have hBlockRank :
        Matrix.rank
            ((finitePronyShiftedHankel (n := n) nodes weights 0).submatrix
              (finInitialEmbedding hmn) (finInitialEmbedding hmn)) = m := by
      rw [finite_prony_hankel_initial_submatrix hmn]
      simpa using Matrix.rank_of_det_ne_zero hDetSquare
    rw [← hBlockRank]
    exact Matrix.rank_submatrix_le
      (finitePronyShiftedHankel (n := n) nodes weights 0)
      (finInitialEmbedding hmn) (finInitialEmbedding hmn)
  have hUpper :
      Matrix.rank
          (finitePronyShiftedHankel (n := n) nodes weights 0) ≤ m := by
    rw [finite_prony_hankel_factorization]
    calc
      Matrix.rank
          (finitePronyVandermonde (n := n) nodes *
            Matrix.diagonal weights *
              (finitePronyVandermonde (n := n) nodes)ᵀ) ≤
          Matrix.rank
            (finitePronyVandermonde (n := n) nodes *
              Matrix.diagonal weights) :=
        Matrix.rank_mul_le_left _ _
      _ ≤ Matrix.rank (finitePronyVandermonde (n := n) nodes) :=
        Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin m) := Matrix.rank_le_card_width _
      _ = m := Fintype.card_fin m
  exact Nat.le_antisymm hUpper hLower

/-- In the separated active-mode regime, the indexed spectral mode count and
the finite Hankel state dimension coincide. -/
theorem finite_prony_mode_count_eq_hankel_rank {m n : ℕ}
    (hmn : m ≤ n) {nodes weights : Fin m → ℂ}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    m = Matrix.rank
      (finitePronyShiftedHankel (n := n) nodes weights 0) :=
  (finite_prony_hankel_rank hmn hNodes hWeights).symm

-- A one-mode active family witnesses the nonempty full-rank regime.
example :
    Matrix.rank
        (finitePronyShiftedHankel
          (n := 1)
          (fun _ : Fin 1 => (2 : ℂ))
          (fun _ : Fin 1 => (3 : ℂ))
          0) = 1 := by
  apply finite_prony_hankel_rank (m := 1) (n := 1) le_rfl
  · intro left right h
    exact Subsingleton.elim left right
  · intro mode
    norm_num

#print axioms square_finitePronyVandermonde_eq_transpose
#print axioms finite_prony_hankel_initial_submatrix
#print axioms finite_prony_hankel_rank
#print axioms finite_prony_mode_count_eq_hankel_rank

end D5.S3.Analytic.GoldenTomography.FinitePronyHankelRank
