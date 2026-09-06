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

/-- The odd Cholesky weights, computed by the Jacobi pivot recurrence. -/
def jacobiPivot (α β : Nat → Real) : Nat → Real
  | 0 => α 0
  | n + 1 => α (n + 1) - β (n + 1) / jacobiPivot α β n

/-- Zero-based indexing of the alternating odd and even Cholesky weights. -/
def jacobiWeights {d : Nat} (α β : Nat → Real) (i : Fin (2 * d - 1)) : Real :=
  if i.val % 2 = 0 then jacobiPivot α β (i.val / 2)
  else β (i.val / 2 + 1) / jacobiPivot α β (i.val / 2)

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

private theorem cholesky_adjacent {d : Nat} {K L : Matrix (Fin d) (Fin d) Real}
    (hLower : L.IsLowerTriangular) (hfactor : K = L * L.transpose)
    (hband : ∀ i j, j.val + 1 < i.val → L i j = 0)
    (j : Nat) (hj : j + 1 < d) :
    K ⟨j + 1, hj⟩ ⟨j, by omega⟩ =
      L ⟨j + 1, hj⟩ ⟨j, by omega⟩ * L ⟨j, by omega⟩ ⟨j, by omega⟩ := by
  rw [hfactor, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  apply Finset.sum_eq_single (⟨j, by omega⟩ : Fin d)
  · intro k _ hk
    by_cases hkj : k.val < j
    · rw [hband _ _ (by dsimp; omega), zero_mul]
    · rw [hLower (show (⟨j, by omega⟩ : Fin d) < k by
        have : k.val ≠ j := fun h => hk (Fin.ext h)
        exact Fin.mk_lt_mk.mpr (by omega)), mul_zero]
  · simp

private theorem cholesky_first {d : Nat} (hd : 0 < d)
    {K L : Matrix (Fin d) (Fin d) Real}
    (hLower : L.IsLowerTriangular) (hfactor : K = L * L.transpose) :
    K ⟨0, hd⟩ ⟨0, hd⟩ = L ⟨0, hd⟩ ⟨0, hd⟩ ^ 2 := by
  rw [hfactor, Matrix.mul_apply, pow_two]
  simp only [Matrix.transpose_apply]
  apply Finset.sum_eq_single (⟨0, hd⟩ : Fin d)
  · intro k _ hk
    rw [hLower (show (⟨0, hd⟩ : Fin d) < k by
      have : k.val ≠ 0 := fun h => hk (Fin.ext h)
      exact Fin.mk_lt_mk.mpr (by omega)), zero_mul]
  · simp

private theorem cholesky_diagonal {d : Nat} {K L : Matrix (Fin d) (Fin d) Real}
    (hLower : L.IsLowerTriangular) (hfactor : K = L * L.transpose)
    (hband : ∀ i j, j.val + 1 < i.val → L i j = 0)
    (j : Nat) (hj : j + 1 < d) :
    K ⟨j + 1, hj⟩ ⟨j + 1, hj⟩ =
      L ⟨j + 1, hj⟩ ⟨j + 1, hj⟩ ^ 2 + L ⟨j + 1, hj⟩ ⟨j, by omega⟩ ^ 2 := by
  let a : Fin d := ⟨j + 1, hj⟩
  let b : Fin d := ⟨j, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  rw [hfactor, Matrix.mul_apply]
  change ∑ k, L a k * L a k = L a a ^ 2 + L a b ^ 2
  calc
    _ = ∑ k ∈ ({a, b} : Finset (Fin d)), L a k * L a k := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      have hka : k ≠ a := hk.1
      have hkb : k ≠ b := hk.2
      have hka' : k.val ≠ j + 1 := fun h => hka (Fin.ext h)
      have hkb' : k.val ≠ j := fun h => hkb (Fin.ext h)
      by_cases hlt : a < k
      · rw [hLower hlt, zero_mul]
      · change ¬ (j + 1 < k.val) at hlt
        rw [hband a k (by change k.val + 1 < j + 1; omega), zero_mul]
    _ = _ := by simp [hab, pow_two]

private theorem jacobi_pivot_eq_cholesky_sq {d : Nat} (hd : 0 < d)
    (α β : Nat → Real) {K L : Matrix (Fin d) (Fin d) Real}
    (hLower : L.IsLowerTriangular) (hfactor : K = L * L.transpose)
    (hdiag : ∀ i, L i i ≠ 0)
    (hband : ∀ i j, j.val + 1 < i.val → L i j = 0)
    (hα : ∀ i : Fin d, K i i = α i.val)
    (hβ : ∀ (j : Nat) (hj : j + 1 < d),
      K ⟨j + 1, hj⟩ ⟨j, by omega⟩ ^ 2 = β (j + 1)) :
    ∀ (j : Nat) (hj : j < d), jacobiPivot α β j = L ⟨j, hj⟩ ⟨j, hj⟩ ^ 2 := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact (hα ⟨0, hj⟩).symm.trans (cholesky_first hd hLower hfactor)
  | succ j ih =>
    intro hj
    have he := cholesky_adjacent hLower hfactor hband j hj
    have hb := hβ j hj
    rw [he, mul_pow] at hb
    have hne : L ⟨j, by omega⟩ ⟨j, by omega⟩ ^ 2 ≠ 0 := pow_ne_zero _ (hdiag _)
    have hquot : β (j + 1) / jacobiPivot α β j =
        L ⟨j + 1, hj⟩ ⟨j, by omega⟩ ^ 2 := by
      rw [ih (by omega), ← hb, mul_div_cancel_right₀ _ hne]
    rw [jacobiPivot, hquot, ← hα ⟨j + 1, hj⟩,
      cholesky_diagonal hLower hfactor hband j hj, add_sub_cancel_right]

/- Preregistered witness: identify the recursively computed pivots with nonzero Cholesky
   diagonal squares. This supplies strict positivity of the differences and all divisors. -/
private theorem jacobi_cholesky_weight_positivity {d : Nat} (hd : 0 < d)
    (α β : Nat → Real) {K : Matrix (Fin d) (Fin d) Real} (hK : K.PosDef)
    (htri : ∀ i j, j.val + 1 < i.val → K i j = 0)
    (hα : ∀ i : Fin d, K i i = α i.val)
    (hβ : ∀ (j : Nat) (hj : j + 1 < d),
      K ⟨j + 1, hj⟩ ⟨j, by omega⟩ ^ 2 = β (j + 1))
    (hβpos : ∀ j, j + 1 < d → 0 < β (j + 1)) :
    (∀ j < d, 0 < jacobiPivot α β j) ∧
      ∀ i : Fin (2 * d - 1), 0 < jacobiWeights α β i := by
  obtain ⟨L, hLower, hfactor, hdiag⟩ := exists_lower_cholesky hK
  have hband := cholesky_bidiagonal_of_tridiagonal hLower hfactor hdiag htri
  have heq := jacobi_pivot_eq_cholesky_sq hd α β hLower hfactor hdiag hband hα hβ
  have hp : ∀ j < d, 0 < jacobiPivot α β j := by
    intro j hj
    rw [heq j hj]
    exact sq_pos_of_ne_zero (hdiag _)
  refine ⟨hp, ?_⟩
  intro i
  dsimp [jacobiWeights]
  split_ifs with hi
  · exact hp _ (by omega)
  · exact div_pos (hβpos _ (by omega)) (hp _ (by omega))

end D5.S3.Constants.Moments.PositiveJacobiCholesky
