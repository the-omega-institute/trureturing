/- GID: D5/S3/Zeros/CriticalPoints/SchurFrobeniusInequality
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/SchurFrobeniusInequality
   mirror-E: none(waiver:general-matrix-inequality)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Basic]
   utility: none
   digest: Schur's eigenvalue inequality with the normality equality criterion. -/

import D5.S3.Quantum.Matrix.CommutatorGap
import D5.S3.Quantum.Matrix.CartesianVariance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Tactic.Linarith

/-! Unitary reduction and the sum of squared moduli of the characteristic roots. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality

open Matrix Complex NormedSpace
open scoped ComplexConjugate

private theorem first_column {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ i : Fin n, (Uᴴ * A * U) i.succ 0 = 0 := by
  let f := Matrix.toEuclideanLin (𝕜 := ℂ) A
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  let u := NormedSpace.normalize v
  have hu : ‖u‖ = 1 := norm_normalize hv.2
  have hfu : f u = μ • u := by
    dsimp [u, NormedSpace.normalize]
    rw [LinearMap.map_smul_of_tower, hv.apply_eq_smul, smul_comm]
  obtain ⟨uU, huU⟩ :=
    D5.S3.Quantum.Matrix.CommutatorGap.exists_unitary_first_column u hu
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := uU
  obtain ⟨hU, hU'⟩ := Unitary.mem_iff.mp uU.prop
  refine ⟨U, hU, hU', ?_⟩
  have hcol : ∀ i, (A * U) i 0 = μ * U i 0 := by
    have hf := congrArg (fun x : EuclideanSpace ℂ (Fin (n + 1)) => x.ofLp) hfu
    simpa [f, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, U, huU] using congrFun hf
  intro i
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [hcol, ← mul_assoc, mul_comm _ μ, mul_assoc, ← Finset.mul_sum]
  have hi := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M i.succ 0) hU
  simpa [Matrix.mul_apply] using congrArg (μ * ·) hi

private def liftIndex (n : ℕ) : Fin (n + 1) ≃ PUnit.{1} ⊕ Fin n :=
  (finSuccEquiv n).trans ((Equiv.optionEquivSumPUnit (Fin n)).trans (Equiv.sumComm _ _))

private def lift {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (Matrix.fromBlocks (1 : Matrix PUnit.{1} PUnit.{1} ℂ) 0 0 V).submatrix (liftIndex n) (liftIndex n)

private theorem lift_mul {n : ℕ} (V W : Matrix (Fin n) (Fin n) ℂ) :
    lift V * lift W = lift (V * W) := by
  simp [lift, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem lift_one (n : ℕ) : lift (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [lift, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private theorem lift_conjTranspose {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    (lift V)ᴴ = lift Vᴴ := by
  simp [lift, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

private theorem lift_triangular {n : ℕ}
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hc : ∀ i : Fin n, C i.succ 0 = 0) (V : Matrix (Fin n) (Fin n) ℂ)
    (ht : (Vᴴ * C.submatrix Fin.succ Fin.succ * V).IsUpperTriangular) :
    (lift Vᴴ * C * lift V).IsUpperTriangular := by
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun i => ?_) i
  · intro h
    exact (Fin.not_lt_zero j h).elim
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      simp [Matrix.mul_apply, Fin.sum_univ_succ, lift, liftIndex, hc]
    · intro h
      simpa [Matrix.mul_apply, Fin.sum_univ_succ, lift, liftIndex, Matrix.submatrix_apply] using
        ht (Fin.succ_lt_succ_iff.mp h)

theorem triangularize (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ (Uᴴ * A * U).IsUpperTriangular := by
  induction n with
  | zero =>
    refine ⟨1, by simp, by simp, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨U, hU, hU', hc⟩ := first_column A
    let C := Uᴴ * A * U
    obtain ⟨V, hV, hV', ht⟩ := ih (C.submatrix Fin.succ Fin.succ)
    have hL : lift V ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
      Unitary.mem_iff.mpr ⟨by
        change (lift V)ᴴ * lift V = 1
        rw [lift_conjTranspose, lift_mul, hV, lift_one], by
        change lift V * (lift V)ᴴ = 1
        rw [lift_conjTranspose, lift_mul, hV', lift_one]⟩
    have hprod := Unitary.mem_iff.mp
      (mul_mem (Unitary.mem_iff.mpr ⟨hU, hU'⟩) hL)
    refine ⟨U * lift V, hprod.1, hprod.2, ?_⟩
    have hh := lift_triangular C hc V ht
    simpa only [C, Matrix.conjTranspose_mul, lift_conjTranspose, Matrix.mul_assoc] using hh

private theorem frobenius_conjugate {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hu : Uᴴ * U = 1) (hu' : U * Uᴴ = 1) :
    ∑ i, ∑ j, ‖(Uᴴ * A * U) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨U, Unitary.mem_iff.mpr ⟨hu, hu'⟩⟩
  have h := (D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right (Uᴴ * A) u).trans
    (D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left A (star u))
  simp only [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum,
    Complex.normSq_eq_norm_sq] at h
  calc
    _ = ∑ i, ∑ j, ‖(Uᴴ * A * U) j i‖ ^ 2 := Finset.sum_comm
    _ = ∑ i, ∑ j, ‖A j i‖ ^ 2 := h
    _ = _ := Finset.sum_comm

private theorem normal_conjugate {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hu : Uᴴ * U = 1) (hu' : U * Uᴴ = 1) :
    (Uᴴ * A * U) * (Uᴴ * A * U)ᴴ = (Uᴴ * A * U)ᴴ * (Uᴴ * A * U) ↔
      A * Aᴴ = Aᴴ * A := by
  let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨U, Unitary.mem_iff.mpr ⟨hu, hu'⟩⟩
  let e := Unitary.conjStarAlgAut ℂ _ (star u)
  simpa only [map_mul, map_star, e, Unitary.conjStarAlgAut_star_apply,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
    (show e (A * star A) = e (star A * A) ↔ A * star A = star A * A from
      e.injective.eq_iff)

private theorem triangular_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (ht : A.IsUpperTriangular) :
    (A.charpoly.roots.map (fun z => ‖z‖ ^ 2)).sum = ∑ i, ‖A i i‖ ^ 2 := by
  rw [Matrix.charpoly_of_isUpperTriangular A ht,
    Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _)]
  simp [List.sum_ofFn]

private theorem normal_triangular_diagonal (n : ℕ) (T : Matrix (Fin n) (Fin n) ℂ)
    (ht : T.IsUpperTriangular) (hn : T * Tᴴ = Tᴴ * T) :
    ∀ i j, i ≠ j → T i j = 0 := by
  induction n with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
    have hcol (i : Fin n) : T i.succ 0 = 0 := ht (Fin.succ_pos i)
    have he := congrArg Complex.re (congrArg (fun M => M 0 0) hn)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Complex.star_def, hcol, map_zero, mul_zero, zero_mul, Finset.sum_const_zero,
      add_zero, Complex.mul_conj, Complex.add_re, Complex.ofReal_re, map_sum] at he
    have hsum : ∑ j : Fin n, ‖T 0 j.succ‖ ^ 2 = 0 := by
      simp_rw [← Complex.normSq_eq_norm_sq]
      have hs : ((starRingEnd ℂ) (T 0 0) * T 0 0).re = normSq (T 0 0) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      rw [hs, Complex.re_sum] at he
      simpa only [Complex.ofReal_re, add_eq_left] using he
    have hrow (j : Fin n) : T 0 j.succ = 0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonneg
        (fun (i : Fin n) _ => sq_nonneg ‖T 0 i.succ‖)).mp hsum j (Finset.mem_univ j)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
    have ht' : (T.submatrix Fin.succ Fin.succ).IsUpperTriangular :=
      fun _ _ h => ht.submatrix (Fin.succ_lt_succ_iff.mpr h)
    have hn' : (T.submatrix Fin.succ Fin.succ) * (T.submatrix Fin.succ Fin.succ)ᴴ =
        (T.submatrix Fin.succ Fin.succ)ᴴ * (T.submatrix Fin.succ Fin.succ) := by
      ext i j
      have hh := congrArg (fun M => M i.succ j.succ) hn
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
        Fin.sum_univ_succ, hrow, hcol] using hh
    have hd := ih (T.submatrix Fin.succ Fin.succ) ht' hn'
    intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact fun h => (h rfl).elim
    · exact fun _ => hrow j
    · exact fun _ => hcol i
    · exact fun h => hd i j (fun e => h (congrArg Fin.succ e))

private theorem diagonal_sum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ‖A i i‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2) ∧
    ((∑ i, ‖A i i‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2) ↔
      ∀ i j, i ≠ j → A i j = 0) := by
  let e := ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2
  have he : 0 ≤ e := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsplit : (∑ i, ‖A i i‖ ^ 2) + e = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    dsimp only [e]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun j => ‖A i j‖ ^ 2) (Finset.mem_univ i)
  refine ⟨by rw [← hsplit]; exact le_add_of_nonneg_right he, ?_⟩
  constructor
  · intro h i j hij
    have he0 : e = 0 := add_eq_left.mp (hsplit.trans h.symm)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖A i j‖)).mp he0 i
      (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖A i j‖)).mp hi j
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
  · intro h
    have he0 : e = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j hj
      simp [h i j (Ne.symm (Finset.ne_of_mem_erase hj))]
    simpa only [he0, add_zero] using hsplit

/-- Schur–Frobenius inequality; equality characterizes normal complex matrices. -/
theorem schur_frobenius (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ((A.charpoly.roots.map (fun μ => ‖μ‖ ^ 2)).sum ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2) ∧
    (((A.charpoly.roots.map (fun μ => ‖μ‖ ^ 2)).sum = ∑ i, ∑ j, ‖A i j‖ ^ 2) ↔
      A * Aᴴ = Aᴴ * A) := by
  obtain ⟨U, hu, hu', ht⟩ := triangularize n A
  let T := Uᴴ * A * U
  have hp : T.charpoly = A.charpoly := by
    dsimp [T]
    let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨U, Unitary.mem_iff.mpr ⟨hu, hu'⟩⟩
    have h := Matrix.charpoly_units_conj' (Unitary.toUnits u) A
    change (U⁻¹ * A * U).charpoly = A.charpoly at h
    rwa [Matrix.inv_eq_left_inv hu] at h
  have hr := triangular_roots T ht
  rw [hp] at hr
  have hf := frobenius_conjugate A U hu hu'
  have hd := diagonal_sum n T
  refine ⟨?_, ?_⟩
  · rw [hr, ← hf]
    exact hd.1
  · rw [hr, ← hf, hd.2, ← normal_conjugate A U hu hu']
    constructor
    · intro h
      have hT : T = Matrix.diagonal (fun i => T i i) := by
        exact (Matrix.IsDiag.diagonal_diag h).symm
      change T * Tᴴ = Tᴴ * T
      rw [hT]
      rw [Matrix.diagonal_conjTranspose]
      exact (Matrix.commute_diagonal _ _).eq
    · exact normal_triangular_diagonal n T ht

end D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality
