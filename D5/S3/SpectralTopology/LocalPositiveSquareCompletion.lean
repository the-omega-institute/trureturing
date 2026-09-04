/- GID: D5/S3/SpectralTopology/LocalPositiveSquareCompletion
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/LocalPositiveSquareCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An off-observer finite real spectrum has a positive
     inverse-square determinant completion. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * Exact and spelling-variant D5 searches covered local positive-square
     completions, shifted inverse squares, resolvent squares, finite hard-core
     determinants, and observer-shifted spectra. No declaration constructs the
     source's matrix from an off-spectrum observer point.
   * `PositiveFredholmLimitZeros.positive_matrix_det_factorization` starts from
     an already positive semidefinite matrix; it does not construct the shifted
     inverse-square spectrum. `FiniteOccupationPartitionFunctions` gives the
     finite fermionic expansion but likewise assumes its diagonal spectrum.
   * Formalization receipts are retired. Digest and generalized-body searches
     found the two adjacent modules above but no theorem with this construction.
   * All remote in-flight lane modules and commit subjects were searched for
     shifted inverse-square and positive determinant formulations; none matched.
   * Pinned Mathlib supplies `Matrix.PosDef.diagonal`, `Matrix.det_diagonal`,
     and `Finset.prod_eq_zero_iff`; they are applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexOrder

namespace D5.S3.SpectralTopology.LocalPositiveSquareCompletion

/-- The inverse-square weight of a spectral value relative to the observer. -/
noncomputable def shiftedInverseSquareEigenvalue {rank : Nat} (spectrum : Fin rank -> Real)
    (observer : Real) (j : Fin rank) : Real :=
  ((spectrum j - observer) ^ 2)⁻¹

/-- The positive-square completion in the diagonal cyclic spectral gauge. -/
noncomputable def localPositiveSquare {rank : Nat} (spectrum : Fin rank -> Real)
    (observer : Real) : Matrix (Fin rank) (Fin rank) Complex :=
  Matrix.diagonal fun j =>
    (shiftedInverseSquareEigenvalue spectrum observer j : Complex)

/-- An observer outside the finite real spectrum produces a positive-definite
inverse-square matrix. Its determinant completion factors over the explicit
positive weights, and every zero of that determinant lies on the strictly
negative real axis. -/
theorem local_positive_square_completion {rank : Nat}
    (spectrum : Fin rank -> Real) (observer : Real)
    (observerOffSpectrum : forall j, spectrum j ≠ observer) :
    (forall j, 0 < shiftedInverseSquareEigenvalue spectrum observer j) ∧
      (localPositiveSquare spectrum observer).PosDef ∧
      (forall w : Complex,
        Matrix.det (1 + w • localPositiveSquare spectrum observer) =
          ∏ j, (1 + w *
            (shiftedInverseSquareEigenvalue spectrum observer j : Complex))) ∧
      (forall w : Complex,
        Matrix.det (1 + w • localPositiveSquare spectrum observer) = 0 ->
          w.im = 0 ∧ w.re < 0) := by
  have eigenvaluePositive
      (j : Fin rank) :
      0 < shiftedInverseSquareEigenvalue spectrum observer j := by
    rw [shiftedInverseSquareEigenvalue]
    exact inv_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr (observerOffSpectrum j)))
  have matrixPositive : (localPositiveSquare spectrum observer).PosDef := by
    unfold localPositiveSquare
    apply Matrix.PosDef.diagonal
    intro j
    exact_mod_cast eigenvaluePositive j
  have determinantFactorization (w : Complex) :
      Matrix.det (1 + w • localPositiveSquare spectrum observer) =
        ∏ j, (1 + w *
          (shiftedInverseSquareEigenvalue spectrum observer j : Complex)) := by
    have diagonalIdentity :
        (1 + w • localPositiveSquare spectrum observer :
            Matrix (Fin rank) (Fin rank) Complex) =
          Matrix.diagonal (fun j =>
            1 + w *
              (shiftedInverseSquareEigenvalue spectrum observer j : Complex)) := by
      ext i j
      by_cases indicesEqual : i = j
      · subst j
        simp [localPositiveSquare]
      · simp [localPositiveSquare, indicesEqual]
    rw [diagonalIdentity, Matrix.det_diagonal]
  refine ⟨eigenvaluePositive, matrixPositive, determinantFactorization, ?_⟩
  intro w determinantZero
  rw [determinantFactorization w, Finset.prod_eq_zero_iff] at determinantZero
  obtain ⟨j, _, factorZero⟩ := determinantZero
  have eigenvalueNonzero :
      (shiftedInverseSquareEigenvalue spectrum observer j : Complex) ≠ 0 := by
    exact_mod_cast (eigenvaluePositive j).ne'
  have productEqualsNegOne :
      w * (shiftedInverseSquareEigenvalue spectrum observer j : Complex) = -1 := by
    calc
      w * (shiftedInverseSquareEigenvalue spectrum observer j : Complex) =
          (1 + w *
            (shiftedInverseSquareEigenvalue spectrum observer j : Complex)) - 1 := by ring
      _ = -1 := by rw [factorZero]; ring
  have observerZero :
      w = ((-1 : Complex) /
        (shiftedInverseSquareEigenvalue spectrum observer j : Complex)) :=
    (eq_div_iff eigenvalueNonzero).2 productEqualsNegOne
  have observerZeroReal :
      w = (((-1 : Real) /
        shiftedInverseSquareEigenvalue spectrum observer j : Real) : Complex) := by
    rw [observerZero]
    norm_num
  rw [observerZeroReal]
  exact ⟨by simp, by
    simp only [Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (eigenvaluePositive j)⟩

/-- If the observer hits a spectral value, Lean's total inverse collapses the
corresponding inverse-square weight to zero. This witnesses why the
off-spectrum hypothesis in `local_positive_square_completion` is necessary. -/
theorem spectral_collision_collapses_inverse_square (observer : Real) :
    shiftedInverseSquareEigenvalue (rank := 1) (fun _ => observer) observer 0 = 0 := by
  simp [shiftedInverseSquareEigenvalue]

#print axioms local_positive_square_completion
#print axioms spectral_collision_collapses_inverse_square

end D5.S3.SpectralTopology.LocalPositiveSquareCompletion
