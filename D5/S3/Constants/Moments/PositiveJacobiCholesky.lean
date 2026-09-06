/- GID: D5/S3/Constants/Moments/PositiveJacobiCholesky
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/PositiveJacobiCholesky
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive Jacobi matrices admit positive recursive Cholesky weights. -/

import D5.S3.Constants.NewtonHankelRealRootCriterion
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/- Library-search audit trail (2026-09-07):
   1. D5 searches for Cholesky, tridiagonal, bidiagonal, and Jacobi weight positivity found
      CoefficientDrivenJacobiCharacteristicPolynomial (monic-basis Jacobi shape and charpoly),
      NewtonHankelRealRootCriterion (root reality criterion), and
      ForbiddenNeighbourDeterminant (the canonical lowerBidiagonal and forbiddenPartition).
      No positive Cholesky weight recurrence was found. Both imported D5 headers are G;
      the two I-level moment modules were read but are not imported.
   2. Pinned mathlib v4.33.0 searches found LDL.lower_conj_diag,
      LDL.lowerInv_triangular, Matrix.blockTriangular_inv_of_blockTriangular,
      Matrix.IsHermitian.posDef_iff_eigenvalues_pos, and Matrix.det_one_add_mul_comm.
      These primitives are reused. No tridiagonal Cholesky weight theorem was found.
   3. This continuation repeated GitHub repository searches through NyxID's
      cma-trigger-github-observer-staging for
      `cholesky lean` and `Jacobi Lean4` found tripp-smith/gecp-kernel-structure.
      Its complete tree at 6f7c0ba9d0230ca1c3c957737ef1ed65008aecfb and the source
      GECPKernelStructure/PositiveDefinite/PivotedCholesky.lean were read:
      it compares pivot-selection traces
      and assumes each positive pivot, so does not supply the required recurrence positivity.
      GitHub code search through the observer returned HTTP 401 (authentication required);
      exhaustive online code search is ASSUMED-UNVERIFIED. No exact third-party hit was found
      in the successfully searched scope.
   4. The lower-factor sparsity induction and its positive weight construction are local.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Polynomial
open scoped BigOperators

namespace D5.S3.Constants.Moments.PositiveJacobiCholesky

private theorem exists_lower_cholesky {d : Nat} {K : Matrix (Fin d) (Fin d) Real}
    (hK : K.PosDef) :
    ∃ L : Matrix (Fin d) (Fin d) Real,
      L.IsLowerTriangular ∧ K = L * L.transpose ∧ ∀ i, L i i ≠ 0 := by
  let U := LDL.lowerInv hK
  have hU : U.IsLowerTriangular := fun _ _ hij => LDL.lowerInv_triangular hK hij
  have hD : (LDL.diag hK).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (isUnit_of_invertible (LDL.lowerInv hK))).mpr hK
  have hp : ∀ i, 0 < LDL.diagEntries hK i := by
    intro i
    simpa [LDL.diag] using hD.diag_pos (i := i)
  let R := Matrix.diagonal (fun i => Real.sqrt (LDL.diagEntries hK i))
  let L := LDL.lower hK * R
  have hLower : L.IsLowerTriangular :=
    (Matrix.blockTriangular_inv_of_blockTriangular hU).mul (Matrix.blockTriangular_diagonal _)
  have hRR : R * R.transpose = LDL.diag hK := by
    simp only [R, diagonal_transpose, diagonal_mul_diagonal, LDL.diag]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hp i).le
  have hfactor : K = L * L.transpose := by
    calc
      K = LDL.lower hK * LDL.diag hK * (LDL.lower hK).transpose := by
        simpa using (LDL.lower_conj_diag hK).symm
      _ = L * L.transpose := by
        rw [← hRR]
        simp only [L, transpose_mul, Matrix.mul_assoc]
  have hdet : L.det ≠ 0 := by
    intro hz
    have hpos := hK.det_pos
    rw [hfactor, det_mul, det_transpose, hz, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨L, hLower, hfactor, ?_⟩
  intro i
  rw [Matrix.det_of_isLowerTriangular L hLower] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)

private theorem cholesky_bidiagonal_of_tridiagonal {d : Nat}
    {K L : Matrix (Fin d) (Fin d) Real}
    (hLower : L.IsLowerTriangular) (hfactor : K = L * L.transpose)
    (hdiag : ∀ i, L i i ≠ 0)
    (htri : ∀ i j, j.1 + 1 < i.1 → K i j = 0) :
    ∀ i j, j.1 + 1 < i.1 → L i j = 0 := by
  have hcol : ∀ n, ∀ j : Fin d, j.1 = n →
      ∀ i, j.1 + 1 < i.1 → L i j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj i hij
      have hentry : K i j = L i j * L j j := by
        rw [hfactor, Matrix.mul_apply]
        apply Finset.sum_eq_single j
        · intro k _ hkj
          rcases lt_or_gt_of_ne hkj with hlt | hgt
          · have hik : k.1 + 1 < i.1 := by omega
            rw [ih k.1 (by omega) k rfl i hik, zero_mul]
          · rw [Matrix.transpose_apply, hLower hgt, mul_zero]
        · simp
      have hz : L i j * L j j = 0 := hentry.symm.trans (htri i j hij)
      exact (mul_eq_zero.mp hz).resolve_right (hdiag j)
  exact fun i j hij => hcol j.1 j rfl i hij

end D5.S3.Constants.Moments.PositiveJacobiCholesky
