/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native singular-value correspondences for actual correlation matrices. -/

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! Adapters for the existing CFC trace norm and native descending singular
values, including zero spectra. No new norm is defined. -/
set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix Module
open scoped BigOperators InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity
namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormSpectral

variable {m n : ℕ}

lemma gram_toEuclideanLin (A : Matrix (Fin m) (Fin n) ℝ) :
    (Aᴴ*A).toEuclideanLin = A.toEuclideanLin.adjoint.comp A.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  ext x i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

private lemma symmetric_eigenvalues_congr
    (T S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (he : T = S)
    (i : Fin (Fintype.card (Fin n))) :
    hT.eigenvalues finrank_euclideanSpace i = hS.eigenvalues finrank_euclideanSpace i := by
  subst S
  rfl

/-- Column-Gram and native zero-extended descending singular values agree. -/
theorem native_singular_value (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin (Fintype.card (Fin n))) :
    A.toEuclideanLin.singularValues i = Real.sqrt
      ((A.posSemidef_conjTranspose_mul_self).isHermitian.eigenvalues₀ i) := by
  rw [A.toEuclideanLin.singularValues_fin finrank_euclideanSpace]
  congr 1
  exact symmetric_eigenvalues_congr _ _ _ _ (gram_toEuclideanLin A).symm i

private lemma native_first_sq (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    A.toEuclideanLin.singularValues 0 ^ 2 =
      A.posSemidef_conjTranspose_mul_self.isHermitian.eigenvalues₀ ⟨0, by simpa using hn⟩ := by
  rw [native_singular_value A ⟨0, by simpa using hn⟩, Real.sq_sqrt]
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
    A.posSemidef_conjTranspose_mul_self.eigenvalues_nonneg
      ((Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (Fintype.card_fin _)) ⟨0, by simpa using hn⟩)

/-- Actual real rectangular CFC trace norm, with every column-side zero retained. -/
theorem traceNorm_eq_native_sum (A : Matrix (Fin m) (Fin n) ℝ) :
    traceNorm A = ∑ i : Fin n, A.toEuclideanLin.singularValues i := by
  let hG := A.posSemidef_conjTranspose_mul_self.isHermitian
  have ht : traceNorm A = ∑ i, Real.sqrt (hG.eigenvalues i) := by
    unfold traceNorm
    rw [CFC.sqrt_eq_real_sqrt (Aᴴ*A)
      (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
      cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq hG, Matrix.IsHermitian.cfc]
    simp [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have he : (∑ i : Fin n, A.toEuclideanLin.singularValues i) =
      ∑ i : Fin (Fintype.card (Fin n)), A.toEuclideanLin.singularValues i :=
    Fintype.sum_equiv (finCongr (Fintype.card_fin n).symm) _ _ (fun _ => rfl)
  rw [ht, he]
  simp_rw [native_singular_value]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun i => Real.sqrt (hG.eigenvalues₀ i))

private lemma native_norm_apply_le (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖A.toEuclideanLin x‖ ≤ A.toEuclideanLin.singularValues 0 * ‖x‖ := by
  by_cases hn : n = 0
  · subst n
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  let G := Aᴴ*A
  let hG := A.posSemidef_conjTranspose_mul_self.isHermitian
  let b := hG.eigenvectorBasis
  have hs (i : Fin n) : ‖A.toEuclideanLin (b i)‖^2 = hG.eigenvalues i := by
    have he := hG.mulVec_eigenvectorBasis i
    have hi : ⟪b i, G.toEuclideanLin (b i)⟫_ℝ = hG.eigenvalues i := by
      change ⟪b i, WithLp.toLp 2 (G.mulVec (b i).ofLp)⟫_ℝ = _
      rw [he]
      simp [b, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [gram_toEuclideanLin] at hi
    simpa [LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq] using hi
  have hex : x = ∑ i, ⟪b i,x⟫_ℝ • b i := by
    simpa only [OrthonormalBasis.repr_apply_apply] using (b.sum_repr x).symm
  have he : ‖A.toEuclideanLin x‖^2 = ∑ i, hG.eigenvalues i * ⟪b i,x⟫_ℝ^2 := by
    have hi : ‖A.toEuclideanLin x‖^2 = ⟪x,G.toEuclideanLin x⟫_ℝ := by
      rw [gram_toEuclideanLin, LinearMap.comp_apply, LinearMap.adjoint_inner_right,
        real_inner_self_eq_norm_sq]
    rw [hi]
    nth_rw 2 [hex]
    simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    have hep : G.toEuclideanLin (b i) = hG.eigenvalues i • b i := by
      apply (WithLp.ofLp_injective 2)
      exact hG.mulVec_eigenvectorBasis i
    rw [hep, real_inner_smul_right, real_inner_comm x (b i)]
    ring
  have hl (i : Fin n) : hG.eigenvalues i ≤ A.toEuclideanLin.singularValues 0 ^ 2 := by
    rw [native_first_sq A (Nat.pos_of_ne_zero hn)]
    apply hG.eigenvalues₀_antitone
    exact Nat.zero_le _
  have hb : ‖A.toEuclideanLin x‖^2 ≤ A.toEuclideanLin.singularValues 0 ^ 2 * ‖x‖^2 := by
    rw [he, ← b.sum_sq_inner_right x, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hl i) (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (A.toEuclideanLin.singularValues_nonneg 0) (norm_nonneg _))).mp
  simpa only [mul_pow] using hb

/-- Infinity is the actual induced Euclidean operator norm. -/
theorem opNorm_eq_native_first (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = A.toEuclideanLin.singularValues 0 := by
  apply le_antisymm
  · change ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ _
    exact ContinuousLinearMap.opNorm_le_bound _ (A.toEuclideanLin.singularValues_nonneg 0)
      (native_norm_apply_le A)
  · by_cases hn : n = 0
    · subst n
      rw [A.toEuclideanLin.singularValues_of_finrank_le (by simp)]
      exact norm_nonneg _
    let hG := A.posSemidef_conjTranspose_mul_self.isHermitian
    let i : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using Nat.pos_of_ne_zero hn⟩
    let j := (Fintype.equivOfCardEq (Fintype.card_fin _)) i
    let e := hG.eigenvectorBasis j
    have he : ‖e‖ = 1 := hG.eigenvectorBasis.orthonormal.1 j
    have hs : ‖A.toEuclideanLin e‖^2 = A.toEuclideanLin.singularValues 0 ^ 2 := by
      rw [native_first_sq A (Nat.pos_of_ne_zero hn)]
      have h := hG.mulVec_eigenvectorBasis j
      have hi : ⟪e,(Aᴴ*A).toEuclideanLin e⟫_ℝ = hG.eigenvalues j := by
        change ⟪e, WithLp.toLp 2 ((Aᴴ*A).mulVec e.ofLp)⟫_ℝ = _
        rw [h]
        change ⟪e, hG.eigenvalues j • e⟫_ℝ = hG.eigenvalues j
        rw [real_inner_smul_right]
        rw [real_inner_self_eq_norm_sq, he]
        ring
      rw [gram_toEuclideanLin, LinearMap.comp_apply, LinearMap.adjoint_inner_right,
        real_inner_self_eq_norm_sq] at hi
      simpa [Matrix.IsHermitian.eigenvalues, j, i] using hi
    have hv : ‖A.toEuclideanLin e‖ = A.toEuclideanLin.singularValues 0 := by
      nlinarith [norm_nonneg (A.toEuclideanLin e), A.toEuclideanLin.singularValues_nonneg 0]
    have hu := Matrix.l2_opNorm_mulVec A e
    change ‖A.toEuclideanLin e‖ ≤ ‖A‖ * ‖e‖ at hu
    simpa [he, hv] using hu

private lemma dualPairing_sub_right (Z : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    dualPairing Z (A-B) = dualPairing Z A - dualPairing Z B := by
  unfold D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity.dualPairing
  rw [map_sub, LinearMap.comp_sub, map_sub]

private lemma dualPairing_sub_left
    (Z W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : Matrix (Fin m) (Fin n) ℝ) :
    dualPairing (Z-W) A = dualPairing Z A - dualPairing W A := by
  unfold D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity.dualPairing
  rw [ContinuousLinearMap.toLinearMap_sub, map_sub, LinearMap.sub_comp, map_sub]

private lemma dualPairing_rankOne (x : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin m) (Fin n) ℝ) :
    dualPairing (InnerProductSpace.rankOne ℝ x y) A = ⟪x,A.toEuclideanLin y⟫_ℝ := by
  unfold D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity.dualPairing
  rw [ContinuousLinearMap.adjoint_toLinearMap, InnerProductSpace.adjoint_rankOne]
  change (ContinuousLinearMap.toLinearMap
    ((InnerProductSpace.rankOne ℝ y x) ∘L A.toEuclideanLin.toContinuousLinearMap)).trace ℝ _ = _
  rw [InnerProductSpace.rankOne_comp, InnerProductSpace.trace_rankOne,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

private lemma complement_rankOne_contraction (e : EuclideanSpace ℝ (Fin m)) (he : ‖e‖ = 1) :
    ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) - InnerProductSpace.rankOne ℝ e e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖x-⟪e,x⟫_ℝ • e‖ ≤ 1*‖x‖
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm x e,
    norm_smul, Real.norm_eq_abs, mul_pow, he, one_pow, mul_one, sq_abs]
  nlinarith [sq_nonneg ⟪e,x⟫_ℝ]

/-- A genuine real rectangular rank-one approximation estimate for the actual
CFC trace norm and induced Euclidean operator norm. Zero vectors are included. -/
theorem traceNorm_sub_rankOne_tail (A : Matrix (Fin m) (Fin n) ℝ)
    (a : EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin n)) :
    traceNorm A - ‖A‖ ≤ traceNorm (A-Matrix.vecMulVec a.ofLp b.ofLp) := by
  classical
  by_cases ha : a = 0
  · simp only [ha, WithLp.ofLp_zero, Matrix.zero_vecMulVec, sub_zero]
    linarith [norm_nonneg A]
  have han : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  let e := ‖a‖⁻¹ • a
  have he : ‖e‖ = 1 := by simp [e, norm_smul, abs_inv, abs_norm, han]
  have hae : a = ‖a‖ • e := by simp [e, smul_smul, han]
  obtain ⟨Z, hZ, hza, _⟩ := traceNorm_eq_max_dualPairing A
  let P := InnerProductSpace.rankOne ℝ e e
  let Q := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) - P
  let W := Q ∘L Z
  have hQ : ‖Q‖ ≤ 1 := complement_rankOne_contraction e he
  have hW : ‖W‖ ≤ 1 := by
    calc
      _ ≤ ‖Q‖*‖Z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1*1 := mul_le_mul hQ hZ (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hzero : dualPairing W (Matrix.vecMulVec a.ofLp b.ofLp) = 0 := by
    rw [dualPairing_outer]
    rw [hae, real_inner_smul_left]
    have hi : ⟪e,W b⟫_ℝ = 0 := by
      change ⟪e,Z b - ⟪e,Z b⟫_ℝ • e⟫_ℝ = 0
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
      ring
    rw [hi, mul_zero]
  have hpc : dualPairing (P ∘L Z) A ≤ ‖A‖ := by
    rw [show P ∘L Z = InnerProductSpace.rankOne ℝ e (Z.adjoint e) from
      InnerProductSpace.rankOne_comp e e Z, dualPairing_rankOne]
    have hz : ‖Z.adjoint e‖ ≤ 1 := by
      have hh := Z.adjoint.le_opNorm e
      rw [ContinuousLinearMap.adjoint.norm_map, he, mul_one] at hh
      exact hh.trans hZ
    calc
      _ ≤ ‖e‖*‖A.toEuclideanLin (Z.adjoint e)‖ := real_inner_le_norm _ _
      _ ≤ 1*(‖A‖*‖Z.adjoint e‖) := by rw [he]; exact mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mulVec A _) (by norm_num)
      _ ≤ ‖A‖ := by nlinarith [norm_nonneg A]
  have hwid : W = Z - P ∘L Z := by ext x; simp [W,Q]
  obtain ⟨_, _, _, hbound⟩ := traceNorm_eq_max_dualPairing (A-Matrix.vecMulVec a.ofLp b.ofLp)
  have hh := hbound W hW
  rw [dualPairing_sub_right, hzero, sub_zero, hwid, dualPairing_sub_left, hza] at hh
  linarith

/-- The complete descending tail through any retained length up to the column
ambient dimension, including all zero values and one-dimensional boundaries. -/
theorem native_tail_le_centered (A : Matrix (Fin m) (Fin n) ℝ)
    (a : EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (∑ i ∈ Finset.Ico 1 k, A.toEuclideanLin.singularValues i) ≤
      traceNorm (A-Matrix.vecMulVec a.ofLp b.ofLp) := by
  have hnorm := traceNorm_sub_rankOne_tail A a b
  rw [traceNorm_eq_native_sum, opNorm_eq_native_first] at hnorm
  have hsum : (∑ i : Fin n, A.toEuclideanLin.singularValues i) =
      A.toEuclideanLin.singularValues 0 + ∑ i ∈ Finset.Ico 1 n, A.toEuclideanLin.singularValues i := by
    rw [← Finset.sum_range]
    have hn : 0 < n := lt_of_lt_of_le (by omega) hkn
    simpa using (Finset.sum_Ico_consecutive
      (fun i => A.toEuclideanLin.singularValues i)
      (by omega : 0 ≤ 1) (by omega : 1 ≤ n)).symm
  have hle : (∑ i ∈ Finset.Ico 1 k, A.toEuclideanLin.singularValues i) ≤
      ∑ i ∈ Finset.Ico 1 n, A.toEuclideanLin.singularValues i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hkn)
    intro i _ _
    exact A.toEuclideanLin.singularValues_nonneg i
  rw [hsum] at hnorm
  linarith

private lemma real_trace_adjoint (f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n)) : f.adjoint.trace ℝ _ = f.trace ℝ _ := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    LinearMap.toMatrix_adjoint]
  rw [Matrix.trace_conjTranspose]
  simp only [star_trivial]
  exact (LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis f).symm

private lemma dualPairing_adjoint (Z : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin m)) (A : Matrix (Fin m) (Fin n) ℝ) :
    dualPairing Z.adjoint A.transpose = dualPairing Z A := by
  unfold D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity.dualPairing
  simp only [ContinuousLinearMap.adjoint_toLinearMap, ContinuousLinearMap.adjoint_adjoint]
  rw [← ContinuousLinearMap.adjoint_toLinearMap,
    ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [LinearMap.trace_comp_comm']
  have he : A.toEuclideanLin.adjoint.comp Z.toLinearMap =
      (Z.toLinearMap.adjoint.comp A.toEuclideanLin).adjoint := by
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  rw [he, real_trace_adjoint]

/-- Transposition preserves the existing real rectangular CFC trace norm. -/
theorem traceNorm_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    traceNorm A.transpose = traceNorm A := by
  have hle (B : Matrix (Fin m) (Fin n) ℝ) : traceNorm B.transpose ≤ traceNorm B := by
    obtain ⟨Z,hZ,hEq,_⟩ := traceNorm_eq_max_dualPairing B.transpose
    obtain ⟨_,_,_,hb⟩ := traceNorm_eq_max_dualPairing B
    have hh := hb Z.adjoint (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hZ)
    have he := dualPairing_adjoint Z B.transpose
    simp only [Matrix.transpose_transpose] at he
    rw [he, hEq] at hh
    exact hh
  apply le_antisymm (hle A)
  obtain ⟨Z,hZ,hEq,_⟩ := traceNorm_eq_max_dualPairing A
  obtain ⟨_,_,_,hb⟩ := traceNorm_eq_max_dualPairing A.transpose
  have hh := hb Z.adjoint (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hZ)
  rw [dualPairing_adjoint, hEq] at hh
  exact hh

/-- The full smaller-side tail is exactly nuclear norm minus operator norm;
all additional ambient singular values are proved zero. -/
theorem native_tail_eq_traceNorm_sub (A : Matrix (Fin m) (Fin n) ℝ)
    (hm : 0 < m) (hn : 0 < n) :
    (∑ i ∈ Finset.Ico 1 (min m n), A.toEuclideanLin.singularValues i) =
      traceNorm A - ‖A‖ := by
  have hr : finrank ℝ A.toEuclideanLin.range ≤ m := by
    simpa using Submodule.finrank_le A.toEuclideanLin.range
  have hz (i : ℕ) (hi : min m n ≤ i) : A.toEuclideanLin.singularValues i = 0 := by
    rcases le_total m n with h | h
    · apply A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr
      exact hr.trans (by simpa only [min_eq_left h] using hi)
    · apply A.toEuclideanLin.singularValues_of_finrank_le
      simpa only [finrank_euclideanSpace, Fintype.card_fin, min_eq_right h] using hi
  have hs : (∑ i ∈ Finset.range n, A.toEuclideanLin.singularValues i) =
      ∑ i ∈ Finset.range (min m n), A.toEuclideanLin.singularValues i := by
    symm
    apply Finset.sum_subset (Finset.range_mono (min_le_right m n))
    intro i _ hi
    exact hz i (by simpa only [Finset.mem_range, not_lt] using hi)
  rw [traceNorm_eq_native_sum, ← Finset.sum_range, hs, opNorm_eq_native_first]
  have hp : 1 ≤ min m n := by omega
  have hh := Finset.sum_Ico_consecutive (fun i => A.toEuclideanLin.singularValues i)
    (by omega : 0 ≤ 1) hp
  simp only [Nat.Ico_zero_eq_range, Finset.sum_range_one] at hh
  linarith

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormSpectral
