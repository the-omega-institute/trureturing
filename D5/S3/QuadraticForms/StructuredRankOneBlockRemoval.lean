/- GID: D5/S3/QuadraticForms/StructuredRankOneBlockRemoval
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/StructuredRankOneBlockRemoval
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Removing a nondegenerate block A X G⁻¹ Xᵀ A subtracts the inertia of G, adds k to the nullity and splits the kernel. -/

import D5.S3.QuadraticForms.StructuredRankOneInertia

/-! Nondegenerate block removal: for a real symmetric `A`, a real `n × k` matrix `X` with
`G = Xᵀ A X` invertible, and `N = A - A X G⁻¹ Xᵀ A`, the inertia of `N` is that of `A` minus that of
`G` with nullity increased by `k`, `ker N = ker A ⊕ im X`, and `rank N = rank A - k`.

The block congruences extend the hyperplane and block-congruence mechanism proposed by Lucid in
MathOverflow question 513954, revision 2 (CC BY-SA 4.0): https://mathoverflow.net/revisions/513954/2 ,
from one vector to a block.

admission_basis: escape-witness. Escape witnesses: upper_block and lower_block (block
congruences of `A ⊕ 0` and of the bordered matrix with corner `G`), removal_inertia, and the public
kernel_split (kernel direct sum, injectivity of `X`, nullity and rank over any field). Consumed
bind-only helper: removal_hermitian. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace D5.S3.QuadraticForms.StructuredRankOneBlockRemoval

open RHLinalg
open D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
open D5.S3.QuadraticForms.StructuredRankOneInertia

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem upper_block (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (X : Matrix ι κ ℝ) :
    (fromBlocks (1 : Matrix ι ι ℝ) X 0 1)ᴴ * fromBlocks A 0 0 (0 : Matrix κ κ ℝ) *
      fromBlocks (1 : Matrix ι ι ℝ) X 0 1 =
      fromBlocks A (A * X) (Xᵀ * A) (Xᵀ * A * X) := by
  have hs : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  simp only [conjTranspose_eq_transpose_of_trivial, fromBlocks_transpose, Matrix.transpose_one,
    Matrix.transpose_zero, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_assoc, hs]

private theorem lower_block (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (X : Matrix ι κ ℝ)
    (hG : IsUnit (Xᵀ * A * X).det) :
    let G := Xᵀ * A * X
    let L := fromBlocks (1 : Matrix ι ι ℝ) 0 (-(G⁻¹ * (Xᵀ * A))) 1
    Lᴴ * fromBlocks A (A * X) (Xᵀ * A) G * L =
      fromBlocks (A - A * X * G⁻¹ * (Xᵀ * A)) 0 0 G := by
  intro G L
  have hs : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hGs : Gᵀ = G := by
    simp only [G, Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  have hGi : (G⁻¹)ᵀ = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hGs]
  have hinv : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have hinv' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
  have hLt : Lᴴ = fromBlocks (1 : Matrix ι ι ℝ) (-(A * X * G⁻¹)) 0 1 := by
    simp only [L, conjTranspose_eq_transpose_of_trivial, fromBlocks_transpose,
      Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_neg, Matrix.transpose_mul,
      hs, hGi, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hLt]
  simp only [L, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc, hinv', hinv]
  congr 1 <;> first | (rw [← Matrix.mul_assoc G, hinv, Matrix.one_mul]; abel) | abel | noncomm_ring


private theorem removal_hermitian (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (X : Matrix ι κ ℝ) :
    (A - A * X * (Xᵀ * A * X)⁻¹ * (Xᵀ * A)).IsHermitian := by
  have hs : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hGs : (Xᵀ * A * X)ᵀ = Xᵀ * A * X := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  apply hA.sub
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.transpose_nonsing_inv,
    hGs, Matrix.mul_assoc]

private theorem removal_inertia (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (X : Matrix ι κ ℝ)
    (hG : IsUnit (Xᵀ * A * X).det) (hGh : (Xᵀ * A * X).IsHermitian) :
    posIndex hA = posIndex (removal_hermitian A hA X) + posIndex hGh ∧
    negIndex hA = negIndex (removal_hermitian A hA X) + negIndex hGh := by
  let G := Xᵀ * A * X
  let U : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks (1 : Matrix ι ι ℝ) X 0 1
  let L : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks (1 : Matrix ι ι ℝ) 0 (-(G⁻¹ * (Xᵀ * A))) 1
  let E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks A (A * X) (Xᵀ * A) G
  have hs : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hU : IsUnit U.det := by simp [U, det_fromBlocks_zero₂₁]
  have hL : IsUnit L.det := by simp [L, det_fromBlocks_zero₁₂]
  have hE : E.IsHermitian := hA.fromBlocks
    (by simp [conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hs]) hGh
  have h0 : (0 : Matrix κ κ ℝ).IsHermitian := isHermitian_zero
  have hbase := blockHermitian hA h0
  have hN := removal_hermitian A hA X
  have heqU := congruence_counts hbase hE U hU (upper_block A hA X)
  have heqL := congruence_counts hE (blockHermitian hN hGh) L hL (lower_block A hA X hG)
  have hb0 := block_counts A _ hA h0
  have hbN := block_counts _ _ hN hGh
  have hz := diagonal_counts (fun _ : κ => (0 : ℝ))
  have hp0 : posIndex h0 = 0 := by simpa using hz.1
  have hn0 : negIndex h0 = 0 := by simpa using hz.2
  constructor <;> omega


section General

variable {K : Type*} [Field K]

/-- The kernel, injectivity, nullity and rank parts of block removal hold for any square matrix over
any field, with no symmetry: if `G = Xᵀ A X` is invertible and `N = A - A X G⁻¹ Xᵀ A`, then `X` is
injective, `ker N = ker A ⊕ im X`, `dim ker N = dim ker A + k` and `rank N + k = rank A`. -/
theorem kernel_split (A : Matrix ι ι K) (X : Matrix ι κ K) (hG : IsUnit (Xᵀ * A * X).det) :
    LinearMap.ker (A - A * X * (Xᵀ * A * X)⁻¹ * (Xᵀ * A)).mulVecLin =
      LinearMap.ker A.mulVecLin ⊔ LinearMap.range X.mulVecLin ∧
    Disjoint (LinearMap.ker A.mulVecLin) (LinearMap.range X.mulVecLin) ∧
    Function.Injective X.mulVecLin ∧
    Module.finrank K (LinearMap.ker (A - A * X * (Xᵀ * A * X)⁻¹ * (Xᵀ * A)).mulVecLin) =
      Module.finrank K (LinearMap.ker A.mulVecLin) + Fintype.card κ ∧
    (A - A * X * (Xᵀ * A * X)⁻¹ * (Xᵀ * A)).rank + Fintype.card κ = A.rank := by
  set G := Xᵀ * A * X with hGdef
  have hinv' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
  have hN : ∀ v, (A - A * X * G⁻¹ * (Xᵀ * A)) *ᵥ v =
      A *ᵥ (v - X *ᵥ (G⁻¹ *ᵥ (Xᵀ *ᵥ (A *ᵥ v)))) := by
    intro v
    simp only [sub_mulVec, mulVec_sub, mulVec_mulVec, Matrix.mul_assoc]
  have hXc : ∀ c, G⁻¹ *ᵥ (Xᵀ *ᵥ (A *ᵥ (X *ᵥ c))) = c := by
    intro c
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, ← hGdef]
    rw [hinv', one_mulVec]
  have hinj : Function.Injective X.mulVecLin := by
    intro c c' h
    have h' : X *ᵥ c = X *ᵥ c' := h
    rw [← hXc c, ← hXc c', h']
  have hk : LinearMap.ker (A - A * X * G⁻¹ * (Xᵀ * A)).mulVecLin =
      LinearMap.ker A.mulVecLin ⊔ LinearMap.range X.mulVecLin := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker, mulVecLin_apply, hN] at hv
      refine Submodule.mem_sup.mpr ⟨v - X *ᵥ (G⁻¹ *ᵥ (Xᵀ *ᵥ (A *ᵥ v))), hv,
        X *ᵥ (G⁻¹ *ᵥ (Xᵀ *ᵥ (A *ᵥ v))), ⟨_, rfl⟩, by abel⟩
    · refine sup_le (fun u hu => ?_) ?_
      · rw [LinearMap.mem_ker, mulVecLin_apply] at hu ⊢
        rw [hN]
        simp only [mulVec_sub, hu, mulVec_mulVec]
        simp only [← mulVec_mulVec, hu, mulVec_zero, sub_zero]
      · rintro _ ⟨c, rfl⟩
        rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, hN, hXc, sub_self, mulVec_zero]
  have hd : Disjoint (LinearMap.ker A.mulVecLin) (LinearMap.range X.mulVecLin) := by
    rw [Submodule.disjoint_def]
    rintro v hv ⟨c, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply] at hv
    have : c = 0 := by
      rw [← hXc c, hv, mulVec_zero, mulVec_zero]
    simp [this]
  have hnul : Module.finrank K (LinearMap.ker (A - A * X * G⁻¹ * (Xᵀ * A)).mulVecLin) =
      Module.finrank K (LinearMap.ker A.mulVecLin) + Fintype.card κ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker A.mulVecLin)
      (LinearMap.range X.mulVecLin)
    rw [disjoint_iff.mp hd, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hinj] at h
    rw [hk, h]
    simp
  refine ⟨hk, hd, hinj, hnul, ?_⟩
  have h1 := (A - A * X * G⁻¹ * (Xᵀ * A)).mulVecLin.finrank_range_add_finrank_ker
  have h2 := A.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card] at h1 h2
  change Matrix.rank _ + _ = _ at h1
  change Matrix.rank _ + _ = _ at h2
  omega

end General

/-- Corollary 3 of Ma and Zhang on MathOverflow 513954 (nondegenerate block removal): for a real
symmetric `A`, a real matrix `X : ι × κ` with `G = Xᵀ A X` invertible, and `N = A - A X G⁻¹ Xᵀ A`,
both `N` and `G` are symmetric, `n₊(A) = n₊(N) + n₊(G)`, `n₋(A) = n₋(N) + n₋(G)`,
`n₀(N) = n₀(A) + k`, `ker N = ker A ⊕ im X` (with `X` injective), and `rank N + k = rank A`, where
`k = |κ|`. -/
theorem result (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (X : Matrix ι κ ℝ)
    (hG : IsUnit (Xᵀ * A * X).det) :
    ∃ (hN : (A - A * X * (Xᵀ * A * X)⁻¹ * (Xᵀ * A)).IsHermitian)
      (hGh : (Xᵀ * A * X).IsHermitian),
      posIndex hA = posIndex hN + posIndex hGh ∧
      negIndex hA = negIndex hN + negIndex hGh ∧
      zeroIndex hN = zeroIndex hA + Fintype.card κ ∧
      LinearMap.ker (A - A * X * (Xᵀ * A * X)⁻¹ * (Xᵀ * A)).mulVecLin =
        LinearMap.ker A.mulVecLin ⊔ LinearMap.range X.mulVecLin ∧
      Disjoint (LinearMap.ker A.mulVecLin) (LinearMap.range X.mulVecLin) ∧
      Function.Injective X.mulVecLin ∧
      (A - A * X * (Xᵀ * A * X)⁻¹ * (Xᵀ * A)).rank + Fintype.card κ = A.rank := by
  have hs : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hGh : (Xᵀ * A * X).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  have hN := removal_hermitian A hA X
  obtain ⟨hp, hn⟩ := removal_inertia A hA X hG hGh
  obtain ⟨hk, hd, hinj, hnul, hrank⟩ := kernel_split A X hG
  refine ⟨hN, hGh, hp, hn, ?_, hk, hd, hinj, hrank⟩
  rw [zeroIndex_eq_nullity, zeroIndex_eq_nullity, hnul]

end D5.S3.QuadraticForms.StructuredRankOneBlockRemoval
