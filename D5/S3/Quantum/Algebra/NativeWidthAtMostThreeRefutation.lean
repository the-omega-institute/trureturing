/- GID: D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation
   generality: E
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: kind=certified-instance
   digest: The native Fin 3 by Fin 5 coefficient event has no width at most three realization. -/

import D5.S3.Quantum.Algebra.CommonCoefficientPlane
import D5.S3.Quantum.Algebra.NativeCoefficientWhitening
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation

abbrev MatM (k : ℕ) := Fin k → Matrix (Fin 3) (Fin 5) ℂ
abbrev MatN (k : ℕ) := Fin k → Matrix (Fin 5) (Fin 3) ℂ

def event : Prop :=
  ∃ k : ℕ, k ≤ 3 ∧ ∃ M : MatM k, ∃ N : MatN k,
    LinearIndependent ℂ M ∧ LinearIndependent ℂ N ∧
      (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
          (∑ r, Matrix.kronecker (M r) (N r)) = 1

private theorem matrix_not_injective_of_dimensions
    {m n : ℕ} (h : n < m) (A : Matrix (Fin n) (Fin m) ℂ) :
    ¬ Function.Injective A.mulVecLin := by
  intro hA
  have hd := LinearMap.finrank_le_finrank_of_injective hA
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  omega

private theorem tensor_kernel_vector
    (M : Matrix (Fin 3) (Fin 5) ℂ) (N : Matrix (Fin 5) (Fin 3) ℂ) :
    ∃ z : Fin 5 → ℂ, z ≠ 0 ∧ M *ᵥ z = 0 ∧
      (Matrix.kronecker M N).mulVec
        (Matrix.vec (Matrix.vecMulVec (fun _ : Fin 3 => 1) z)) = 0 := by
  have hnot : ¬ Function.Injective M.mulVecLin :=
    matrix_not_injective_of_dimensions (m := 5) (n := 3) (by omega) M
  obtain ⟨x, y, hxyM, hxy⟩ := Function.not_injective_iff.mp hnot
  let z := x - y
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy
  have hMz : M *ᵥ z = 0 := by
    dsimp [z]
    change M.mulVecLin (x - y) = 0
    rw [map_sub, hxyM, sub_self]
  refine ⟨z, hz, hMz, ?_⟩
  have hvec := Matrix.kronecker_mulVec_vec N
    (Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℂ)) z) M
  have hright : Matrix.vecMulVec (fun _ : Fin 3 => 1) z * Mᵀ = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply,
      one_mul]
    simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hMz j
  have hv0 : Matrix.vec (N * Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℂ)) z * Mᵀ) = 0 := by
    rw [Matrix.mul_assoc, hright, Matrix.mul_zero]
    simp
  simpa [Matrix.kronecker] using hvec.trans hv0

private theorem gram_identity_injective
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (F : Matrix m n ℂ) (hF : Fᴴ * F = 1) : Function.Injective F.mulVecLin := by
  intro u v huv
  have hzero : F *ᵥ (u - v) = 0 := by
    change F.mulVecLin (u - v) = 0
    rw [map_sub, huv, sub_self]
  have hleft : (Fᴴ * F) *ᵥ (u - v) = 0 := by
    rw [← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero]
  rw [hF, Matrix.one_mulVec] at hleft
  exact sub_eq_zero.mp hleft

private theorem k_zero_false
    (M : MatM 0) (N : MatN 0)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1) : False := by
  have h := congrArg (fun A : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ =>
    A (0, 0) (0, 0)) hF
  simpa [Matrix.one_apply] using h

private theorem k_one_false
    (M : MatM 1) (N : MatN 1)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1) : False := by
  let F := Matrix.kronecker (M 0) (N 0)
  have hsum : (∑ r, Matrix.kronecker (M r) (N r)) = F := by
    simp [F]
  have hFinj : Function.Injective F.mulVecLin := by
    apply gram_identity_injective F
    simpa [F, hsum] using hF
  obtain ⟨z, hz, hMz, hker⟩ := tensor_kernel_vector (M 0) (N 0)
  have hvzero : Matrix.vec (Matrix.vecMulVec (fun _ : Fin 3 => 1) z) = 0 := by
    apply hFinj
    simpa [F] using hker
  have hmatzero : Matrix.vecMulVec (fun _ : Fin 3 => 1) z = 0 := by
    exact Matrix.vec_eq_zero_iff.mp hvzero
  have hone : (fun _ : Fin 3 => (1 : ℂ)) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  apply hz
  funext j
  have hj := congrArg (fun A => A 0 j) hmatzero
  simpa [Matrix.vecMulVec_apply] using hj

private theorem rank_kronecker_one_general
    {m n : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix.kronecker H (1 : Matrix (Fin n) (Fin n) ℂ)).rank = n * H.rank := by
  classical
  let e : (Fin m × Fin n) ≃ (Σ _ : Fin n, Fin m) :=
    (Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm
  have he : (Matrix.blockDiagonal' (fun _ : Fin n => H)).submatrix e e =
      Matrix.kronecker H (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext ⟨r, i⟩ ⟨s, j⟩
    by_cases hij : i = j
    · subst j
      simp [e, Matrix.kronecker, Matrix.kroneckerMap_apply]
    · simp [e, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.blockDiagonal'_apply_ne, hij]
  rw [← he, Matrix.rank_submatrix,
    D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Blocks.rank_block]
  simp

private theorem two_compression_zero
    (S : Matrix (Fin 2 × Fin 3) (Fin 5) ℂ)
    (hinj : Function.Injective S.mulVecLin)
    (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hT : Sᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) * S = 0) :
    T = 0 := by
  have hS : S.rank = 5 := by
    change finrank ℂ (LinearMap.range S.mulVecLin) = 5
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  by_contra hne
  have hTr : 0 < T.rank := by
    rw [Matrix.rank]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    have hentry : ∃ i j, T i j ≠ 0 := by
      by_contra h'
      push_neg at h'
      apply hne
      ext i j
      exact h' i j
    obtain ⟨i, j, hij⟩ := hentry
    refine ⟨⟨T *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩, ?_⟩
    intro hv
    have hv' := congrArg Subtype.val hv
    have hvi := congrFun hv' i
    fin_cases j
    · simp [Matrix.mulVec, dotProduct] at hvi
      apply hij
      change T i 0 = 0
      exact hvi
    · simp [Matrix.mulVec, dotProduct] at hvi
      apply hij
      change T i 1 = 0
      exact hvi
  let Q := Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ)
  have hQ : Q.rank = 3 * T.rank := rank_kronecker_one_general T
  have hleft := Matrix.rank_mul_ge Sᴴ Q
  have hright := Matrix.rank_mul_ge (Sᴴ * Q) S
  have hz : (Sᴴ * Q * S).rank = 0 := by rw [show Sᴴ * Q * S = 0 from hT]; simp
  simp only [Matrix.rank_conjTranspose, hS, Fintype.card_prod,
    Fintype.card_fin] at hleft hright
  rw [hQ] at hleft
  omega

private def stackK {k : ℕ} (M : MatM k) : Matrix (Fin k × Fin 3) (Fin 5) ℂ :=
  fun p j => M p.1 p.2 j

private theorem stackK_gram {k : ℕ} (M : MatM k) :
    (stackK M)ᴴ * stackK M = ∑ r, (M r)ᴴ * M r := by
  ext i j
  simp only [stackK, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]

private theorem block_kernel {k : ℕ}
    (M : MatM k) (N : MatN k)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1)
    (l m : Fin 3) :
    ∑ r, ∑ s, (((N r)ᴴ * N s) l m -
      (if r = s then if l = m then 1 else 0 else 0)) • ((M r)ᴴ * M s) = 0 := by
  have hExp : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) =
      ∑ r, ∑ s, Matrix.kronecker ((M r)ᴴ * M s) ((N r)ᴴ * N s) := by
    simp only [Matrix.kronecker, Matrix.conjTranspose_sum, Matrix.sum_mul,
      Matrix.mul_sum, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    exact Finset.sum_comm
  rw [hExp] at hF
  ext u v
  have h := congrArg (fun A : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ =>
    A (u, l) (v, m)) hF
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq] at h
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.zero_apply]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have h' : ∑ r, ∑ s, ((N r)ᴴ * N s) l m * ((M r)ᴴ * M s) u v =
      (if u = v ∧ l = m then 1 else 0) := by
    simpa [mul_comm] using h
  rw [h']
  have hdelta :
      ∑ r, ∑ s, (if r = s then if l = m then 1 else 0 else 0) *
          ((M r)ᴴ * M s) u v =
        (if l = m then (∑ r, (M r)ᴴ * M r) u v else 0) := by
    by_cases hlm : l = m
    · subst m
      simp [Matrix.sum_apply]
    · simp [hlm]
  rw [hdelta]
  have hMEntry (a b : Fin 5) :
      (∑ r, (M r)ᴴ * M r) a b = (if a = b then 1 else 0) := by
    simpa [Matrix.one_apply] using congrArg
      (fun A : Matrix (Fin 5) (Fin 5) ℂ => A a b) hMGram
  by_cases huv : u = v
  · subst v
    by_cases hlm : l = m
    · rw [hMEntry]
      simp [hlm]
    · rw [hMEntry]
      simp [hlm]
  · by_cases hlm : l = m
    · rw [hMEntry]
      simp [huv, hlm]
    · simp [huv, hlm]

end D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
