/- GID: D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation
   generality: E
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: kind=certified-instance
   digest: Native k3 common-plane consumer refuted by compression rank. -/

import D5.S3.Quantum.Algebra.CommonCoefficientPlane
import D5.S3.Quantum.Algebra.NativeCoefficientWhitening
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.Module
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

private theorem stackK_compression_conjTranspose
    (M : MatM 3) (T : Matrix (Fin 3) (Fin 3) ℂ) :
    (stackK M)ᴴ * Matrix.kronecker Tᴴ (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M =
      ((stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) *
        stackK M)ᴴ := by
  have hk : (Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ =
      Matrix.kronecker Tᴴ (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    simpa only [Matrix.kronecker, Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ)
  rw [← hk]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

private theorem block_compression
    (M : MatM 3) (N : MatN 3)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1) (l m : Fin 3) :
    let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
      ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
    (stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) *
      stackK M = 0 := by
  let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
    ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
  change (stackK M)ᴴ * Matrix.kronecker T
      (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0
  change D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M T = 0
  rw [D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum]
  exact block_kernel M N hF hMGram l m

private theorem stackK_compression_smul_add
    (M : MatM 3) (a b : ℂ) (T U : Matrix (Fin 3) (Fin 3) ℂ) :
    (stackK M)ᴴ * Matrix.kronecker (a • T + b • U)
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M =
      a • ((stackK M)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M) +
      b • ((stackK M)ᴴ * Matrix.kronecker U
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M) := by
  change D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M (a • T + b • U) =
    a • D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M T +
    b • D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression M U
  rw [D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum,
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum,
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression_eq_sum]
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul,
    add_smul, smul_add]

private theorem complex_block_neutral
    (M : MatM 3) (N : MatN 3)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1)
    (L : Submodule ℂ (Fin 3 → ℂ))
    (hplane : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      (stackK M)ᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) *
        stackK M = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0)
    (l m : Fin 3) :
    ∀ u ∈ L, ∀ v ∈ L,
      star u ⬝ᵥ ((fun r s =>
        ((N r)ᴴ * N s) l m -
          (if r = s then if l = m then 1 else 0 else 0)) *ᵥ v) = 0 := by
  let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
    ((N r)ᴴ * N s) l m - (if r = s then if l = m then 1 else 0 else 0)
  let Tr : Matrix (Fin 3) (Fin 3) ℂ := (realPart T : Matrix (Fin 3) (Fin 3) ℂ)
  let Ti : Matrix (Fin 3) (Fin 3) ℂ :=
    (imaginaryPart T : Matrix (Fin 3) (Fin 3) ℂ)
  have hc : (stackK M)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
    exact block_compression M N hF hMGram l m
  have hcstar : (stackK M)ᴴ * Matrix.kronecker Tᴴ
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
    rw [stackK_compression_conjTranspose, hc, Matrix.conjTranspose_zero]
  have hc' : (stackK M)ᴴ * Matrix.kroneckerMap (fun x y : ℂ => x * y) T
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
    simpa [Matrix.kronecker] using hc
  have hcstar' : (stackK M)ᴴ * Matrix.kroneckerMap (fun x y : ℂ => x * y) Tᴴ
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
    simpa [Matrix.kronecker] using hcstar
  have hTr : Tr.IsHermitian := by
    exact (realPart T).property.isHermitian
  have hTi : Ti.IsHermitian := by
    exact (imaginaryPart T).property.isHermitian
  have hTr_formula : Tr = ((2 : ℝ)⁻¹ : ℂ) • (T + Tᴴ) := by
    dsimp [Tr]
    rw [realPart_apply_coe]
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul]
    ring
  let c : ℂ := -Complex.I * ((2 : ℝ)⁻¹ : ℂ)
  have hTi_formula : Ti = c • (T - Tᴴ) := by
    dsimp [Ti]
    rw [imaginaryPart_apply_coe]
    ext i j
    simp [c, Matrix.star_eq_conjTranspose, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul, smul_smul]
    ring
  have hcTr : (stackK M)ᴴ * Matrix.kronecker Tr
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
    rw [hTr_formula]
    calc
      _ = (stackK M)ᴴ * Matrix.kroneckerMap (fun x y : ℂ => x * y)
          (((2 : ℝ)⁻¹ : ℂ) • T + ((2 : ℝ)⁻¹ : ℂ) • Tᴴ)
          (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M := by
              simp [Matrix.kronecker, Matrix.star_eq_conjTranspose, smul_add]
      _ = ((2 : ℝ)⁻¹ : ℂ) • ((stackK M)ᴴ * Matrix.kroneckerMap
          (fun x y : ℂ => x * y) T (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M) +
          ((2 : ℝ)⁻¹ : ℂ) • ((stackK M)ᴴ * Matrix.kroneckerMap
          (fun x y : ℂ => x * y) Tᴴ (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M) := by
            simpa [Matrix.kronecker] using
              stackK_compression_smul_add M ((2 : ℝ)⁻¹ : ℂ) ((2 : ℝ)⁻¹ : ℂ) T Tᴴ
      _ = 0 := by rw [hc', hcstar']; simp
  have hcTi : (stackK M)ᴴ * Matrix.kronecker Ti
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M = 0 := by
    rw [hTi_formula]
    have h := stackK_compression_smul_add M c (-c) T Tᴴ
    calc
      _ = (stackK M)ᴴ * Matrix.kroneckerMap (fun x y : ℂ => x * y)
          (c • T + (-c) • Tᴴ) (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M := by
              simp [Matrix.kronecker, c, Matrix.star_eq_conjTranspose,
                sub_eq_add_neg, smul_add, smul_sub, smul_neg, smul_smul,
                smul_eq_mul]
      _ = c • ((stackK M)ᴴ * Matrix.kroneckerMap (fun x y : ℂ => x * y)
          T (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M) +
          (-c) • ((stackK M)ᴴ * Matrix.kroneckerMap (fun x y : ℂ => x * y)
          Tᴴ (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M) := by
            simpa [Matrix.kronecker] using h
      _ = 0 := by rw [hc', hcstar']; simp
  intro u hu v hv
  have hr := hplane Tr hTr hcTr u hu v hv
  have hi := hplane Ti hTi hcTi u hu v hv
  have hdecomp : Tr + Complex.I • Ti = T := by
    exact realPart_add_I_smul_imaginaryPart T
  change star u ⬝ᵥ (T *ᵥ v) = 0
  rw [← hdecomp]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, hr, hi]
  simp

private def coefficientColumns (N : MatN 3) :
    Matrix (Fin 5) (Fin 3 × Fin 3) ℂ := fun j p => N p.1 j p.2

private theorem coefficient_columns_gram (N : MatN 3) (r s l m : Fin 3) :
    ((coefficientColumns N)ᴴ * coefficientColumns N) (r, l) (s, m) =
      ((N r)ᴴ * N s) l m := by
  simp [coefficientColumns, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem native_three_refutation
    (M : MatM 3) (N : MatN 3) (hM : LinearIndependent ℂ M)
    (hN : LinearIndependent ℂ N) :
    ¬ ((∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1) := by
  intro hF
  obtain ⟨B, hB, hBB, hPres, hMGram, _hNGram, hMprimeLI⟩ :=
    D5.S3.Quantum.Algebra.NativeCoefficientWhitening.exact_whitening M N hN hF
  let M' : MatM 3 := D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix B M
  let Ccoeff : Matrix (Fin 3) (Fin 3) ℂ := B.transpose⁻¹
  let N' : MatN 3 := D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix Ccoeff N
  have hM'LI : LinearIndependent ℂ M' := by
    simpa [M'] using hMprimeLI hM
  have hM'Gram : ∑ r, (M' r)ᴴ * M' r = 1 := by
    simpa [M'] using hMGram
  have hF' : (∑ r, Matrix.kronecker (M' r) (N' r))ᴴ *
      (∑ r, Matrix.kronecker (M' r) (N' r)) = 1 := by
    have hPres0 : (∑ r, Matrix.kronecker (M' r) (N' r)) =
        ∑ r, Matrix.kronecker (M r) (N r) := by
      simpa [M', N', Ccoeff] using hPres
    calc
      (∑ r, Matrix.kronecker (M' r) (N' r))ᴴ *
          (∑ r, Matrix.kronecker (M' r) (N' r)) =
          (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
            (∑ r, Matrix.kronecker (M r) (N r)) := by
              exact congrArg
                (fun A : Matrix (Fin 3 × Fin 5) (Fin 5 × Fin 3) ℂ => Aᴴ * A) hPres0
      _ = 1 := hF
  have hstackGram : (stackK M')ᴴ * stackK M' = 1 := by
    rw [stackK_gram]
    exact hM'Gram
  have hstackInj : Function.Injective (stackK M').mulVecLin :=
    gram_identity_injective (stackK M') hstackGram
  obtain ⟨L, hLdim, hL⟩ :=
    D5.S3.Quantum.Algebra.CommonCoefficientPlane.common_plane M' hM'LI hstackInj
  have hplane : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      (stackK M')ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin 3) (Fin 3) ℂ) * stackK M' = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
    intro T hT hcomp u hu v hv
    have hcomp' : (D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M')ᴴ *
        Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) *
          D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M' = 0 := by
      have hs : D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack M' =
          stackK M' := rfl
      rw [hs]
      exact hcomp
    exact hL T hT hcomp' u hu v hv
  have hneutral := complex_block_neutral M' N' hF' hM'Gram L hplane
  let e : (Fin 3 → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
    (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)).symm
  let Le : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) := L.map e.toLinearMap
  have hLedim : finrank ℂ Le = 2 := by
    rw [LinearEquiv.finrank_map_eq e, hLdim]
  let b : OrthonormalBasis (Fin 2) ℂ Le := hLedim ▸ stdOrthonormalBasis ℂ Le
  let V : Matrix (Fin 3) (Fin 2) ℂ := fun i a =>
    (WithLp.ofLp ((b a : Le) : EuclideanSpace ℂ (Fin 3))) i
  have hVgram : Vᴴ * V = 1 := by
    ext a c
    have hb := (orthonormal_iff_ite.mp b.orthonormal) a c
    simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply,
      PiLp.inner_apply, dotProduct, Matrix.one_apply, mul_comm] using hb
  have hVplane : ∀ (l m : Fin 3) (a c : Fin 2),
      ∑ r, ∑ s, star (V r a) *
        (((N' r)ᴴ * N' s) l m -
          (if r = s then if l = m then 1 else 0 else 0)) * V s c = 0 := by
    intro l m a c
    obtain ⟨u, hu, hueq⟩ := (b a).property
    obtain ⟨v, hv, hveq⟩ := (b c).property
    have hVa (r : Fin 3) : V r a = u r := by
      have hh := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => WithLp.ofLp z r) hueq
      simpa [V, e] using hh.symm
    have hVc (r : Fin 3) : V r c = v r := by
      have hh := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => WithLp.ofLp z r) hveq
      simpa [V, e] using hh.symm
    have hh := hneutral l m u hu v hv
    simpa [Matrix.mulVec, dotProduct, hVa, hVc, Finset.mul_sum,
      Finset.sum_mul, mul_assoc] using hh
  let W : Matrix (Fin 5) (Fin 3 × Fin 3) ℂ := coefficientColumns N'
  let P : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Wᴴ * W
  let C : Matrix (Fin 3 × Fin 3) (Fin 2 × Fin 3) ℂ :=
    Matrix.kronecker V (1 : Matrix (Fin 3) (Fin 3) ℂ)
  have hPentry (r s l m : Fin 3) : P (r, l) (s, m) =
      ((N' r)ᴴ * N' s) l m := by
    simpa [P, W] using coefficient_columns_gram N' r s l m
  have hCPC : Cᴴ * P * C = 1 := by
    have hCentry (r i : Fin 3) (a : Fin 2) (l : Fin 3) :
        C (r, i) (a, l) = if i = l then V r a else 0 := by
      by_cases h : i = l <;> simp [C, Matrix.kronecker,
        Matrix.kroneckerMap_apply, h]
    ext ⟨a, l⟩ ⟨c, m⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.conjTranspose_apply]
    simp_rw [hCentry, hPentry]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.sum_mul, Finset.mul_sum]
    have hz := hVplane l m a c
    have hv : ∑ r, ∑ s, star (V r a) *
        ((if r = s then if l = m then 1 else 0 else 0)) * V s c =
        (if l = m then (Vᴴ * V) a c else 0) := by
      by_cases hlm : l = m
      · subst m
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
          Finset.sum_mul, Finset.mul_sum]
      · simp [hlm]
    have hsum (r s : Fin 3) :
        ∑ i : Fin 3, star (if i = l then V r a else 0) *
          ((N' r)ᴴ * N' s) i m * V s c =
          star (V r a) * ((N' r)ᴴ * N' s) l m * V s c := by
      classical
      rw [Finset.sum_eq_single l]
      · simp
      · intro b hb hbl
        simp [hbl]
      · simp
    simp_rw [hsum]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib] at hz
    rw [hv, hVgram] at hz
    rw [Finset.sum_comm]
    by_cases hac : a = c <;> by_cases hlm : l = m
    · simpa [Matrix.one_apply, Prod.mk.injEq, hac, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, hac, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, hac, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, hac, hlm] using sub_eq_zero.mp hz
  have hRank : (Cᴴ * P * C).rank ≤ 5 := by
    calc
      (Cᴴ * P * C).rank ≤ P.rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      _ ≤ W.rank := Matrix.rank_mul_le_right _ _
      _ ≤ 5 := by simpa using W.rank_le_card_height
  rw [hCPC, Matrix.rank_one] at hRank
  norm_num at hRank

end D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
