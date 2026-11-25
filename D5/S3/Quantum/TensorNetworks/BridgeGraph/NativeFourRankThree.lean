/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourRankThree
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourRankThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Right dimension bounds from a rank-three Hermitian compression kernel. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree

/-! A rank-three coefficient isolates a right isometry and a low-rank orthogonal factor. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree

open NativeRectangularBound (reduce_left)
open D5.S3.Quantum.Algebra.NativeCoefficientWhitening (mix)
open D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
  (rank_kronecker_one_general)
private theorem sub_kron {a b c d : ℕ} (A B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin d) (Fin c) ℂ) : kronecker (A - B) C = kronecker A C - kronecker B C := by
  change (Matrix.kroneckerBilinear (R := ℂ)) (A - B) C = _
  rw [map_sub, LinearMap.sub_apply]
  rfl

private theorem kron_sub {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (B C : Matrix (Fin d) (Fin c) ℂ) : kronecker A (B - C) = kronecker A B - kronecker A C := by
  change (Matrix.kroneckerBilinear (R := ℂ)) A (B - C) = _
  rw [map_sub]
  rfl

private theorem column_rank {a b c d : ℕ} (F : Matrix (Fin a × Fin d) (Fin b × Fin c) ℂ)
    (hF : Fᴴ * F = 1) : F.rank = b * c := by
  rw [← Matrix.rank_conjTranspose_mul_self F, hF, Matrix.rank_one,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

private theorem row_defect_rank {a b c d : ℕ} (F : Matrix (Fin a × Fin d) (Fin b × Fin c) ℂ)
    (hF : Fᴴ * F = 1) : (1 - F * Fᴴ).rank ≤ a * d - b * c := by
  have hzero : (1 - F * Fᴴ) * F = 0 := by
    simp [Matrix.sub_mul, Matrix.mul_assoc, hF]
  have hr := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  rw [column_rank F hF, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hr
  omega

/-- A slice larger than the row defect forces the paired left factor to be a coisometry. -/
private theorem small_defect_compression {a b c d e : ℕ}
    (F : Matrix (Fin a × Fin d) (Fin b × Fin c) ℂ)
    (hF : Fᴴ * F = 1)
    (X : Matrix (Fin a) (Fin b) ℂ)
    (E : Matrix (Fin d) (Fin e) ℂ)
    (hcomp :
      (kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E)ᴴ *
        (1 - F * Fᴴ) * kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E =
      kronecker (1 - X * Xᴴ) (1 : Matrix (Fin e) (Fin e) ℂ)) :
    e * (1 - X * Xᴴ).rank ≤ a * d - b * c ∧
      (a * d - b * c < e → X * Xᴴ = 1) := by
  classical
  have hdefect := row_defect_rank F hF
  have hcompress :
      ((kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E)ᴴ *
        (1 - F * Fᴴ) * kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E).rank ≤
        (1 - F * Fᴴ).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hcomp, rank_kronecker_one_general] at hcompress
  have hbound : e * (1 - X * Xᴴ).rank ≤ a * d - b * c := by omega
  refine ⟨hbound, ?_⟩
  intro hsmall
  have hzeroRank : (1 - X * Xᴴ).rank = 0 := by
    by_contra h
    have hp : 1 ≤ (1 - X * Xᴴ).rank := by omega
    have hm := Nat.mul_le_mul_left e hp
    omega
  have hlin : (1 - X * Xᴴ).mulVecLin = 0 :=
    LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hzeroRank)
  have hz : 1 - X * Xᴴ = 0 := by
    have h := congrArg LinearMap.toMatrix' hlin
    simpa only [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', map_zero] using h
  exact (sub_eq_zero.mp hz).symm

/-- Nested kernels for three left factors isolate the fourth right factor. -/
private theorem orthogonal_combination_of_one_direction_kernel {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hab : a < b)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ *
      (∑ i, kronecker (X i) (Y i)) = 1)
    (hX : ∑ i, (X i)ᴴ * X i = 1)
    (hker : ∀ x : Fin b → ℂ, X 0 *ᵥ x = 0 →
      X 1 *ᵥ x = 0 ∧ X 2 *ᵥ x = 0) :
    (Y 3)ᴴ * Y 3 = 1 ∧
      ∃ v : Fin 4 → ℂ, v ≠ 0 ∧ v 3 = 0 ∧
        (Y 3)ᴴ * (∑ i, v i • Y i) = 0 := by
  classical
  let K := LinearMap.ker (X 0).mulVecLin
  let f := (X 3).mulVecLin.domRestrict K
  have hstack : Function.Injective (NativeRectangularBound.stackK X).mulVecLin := by
    apply D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation.gram_identity_injective
    rw [NativeRectangularBound.stackK_gram, hX]
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    have hx0 : X 0 *ᵥ x.val = 0 := x.property
    obtain ⟨hx1, hx2⟩ := hker x.val hx0
    have hx3 : X 3 *ᵥ x.val = 0 := hx
    have hall (r : Fin 4) : X r *ᵥ x.val = 0 := by
      fin_cases r <;> assumption
    apply hstack
    ext ⟨r, j⟩
    change ((NativeRectangularBound.stackK X).mulVecLin x.val) (r, j) =
      ((NativeRectangularBound.stackK X).mulVecLin 0) (r, j)
    rw [map_zero, Pi.zero_apply]
    exact congrFun (hall r) j
  let D := LinearMap.range (X 0).mulVecLin
  let R := LinearMap.range f
  have hdimR : finrank ℂ R = finrank ℂ K := LinearMap.finrank_range_of_inj hf
  have hdimK := (X 0).mulVecLin.finrank_range_add_finrank_ker
  change finrank ℂ D + finrank ℂ K = _ at hdimK
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdimK
  have hsup := (D ⊔ R).finrank_le
  have hdim := D.finrank_sup_add_finrank_inf_eq R
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsup
  have hpos : 0 < finrank ℂ (D ⊓ R : Submodule ℂ (Fin a → ℂ)) := by omega
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hw0 : w.val ≠ 0 := by intro h; exact hw (Subtype.ext h)
  obtain ⟨z, hz⟩ := w.property.1
  obtain ⟨u, hu⟩ := w.property.2
  have hu0 : X 0 *ᵥ u.val = 0 := u.property
  obtain ⟨hu1, hu2⟩ := hker u.val hu0
  have hu3 : X 3 *ᵥ u.val = w.val := hu
  have hz0 : X 0 *ᵥ z = w.val := hz
  have hn : star w.val ⬝ᵥ w.val ≠ 0 :=
    fun h => hw0 (dotProduct_star_self_eq_zero.mp h)
  have hpair (T : Matrix (Fin 4) (Fin 4) ℂ)
      (hT : NativeFourKernel.compression X T = 0) (x y : Fin b → ℂ) :
      ∑ r, ∑ s, T r s * (star (X r *ᵥ x) ⬝ᵥ (X s *ᵥ y)) = 0 := by
    have h := congrArg (fun A : Matrix (Fin b) (Fin b) ℂ => star x ⬝ᵥ (A *ᵥ y)) hT
    rw [NativeFourKernel.compression, NativeRectangularBound.stackK_compression] at h
    simpa only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Matrix.zero_mulVec, dotProduct_zero,
      D5.S3.Quantum.Algebra.CommonCoefficientPlane.cross_pairing] using h
  have h33 (T : Matrix (Fin 4) (Fin 4) ℂ)
      (hT : NativeFourKernel.compression X T = 0) : T 3 3 = 0 := by
    have h := hpair T hT u.val u.val
    simp only [Fin.sum_univ_four, hu0, hu1, hu2, hu3, star_zero,
      dotProduct_zero, zero_dotProduct, mul_zero, zero_add, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hn
  let v : Fin 4 → ℂ := ![star w.val ⬝ᵥ (X 0 *ᵥ z),
    star w.val ⬝ᵥ (X 1 *ᵥ z), star w.val ⬝ᵥ (X 2 *ᵥ z), 0]
  have hv : v ≠ 0 := by
    intro h
    apply hn
    have hv0 := congrFun h 0
    simpa [v, hz0] using hv0
  have hrow (T : Matrix (Fin 4) (Fin 4) ℂ)
      (hT : NativeFourKernel.compression X T = 0) :
      ∑ s, T 3 s * v s = 0 := by
    have h := hpair T hT u.val z
    simpa [Fin.sum_univ_four, hu0, hu1, hu2, hu3, h33 T hT, v] using h
  let T (l m : Fin c) : Matrix (Fin 4) (Fin 4) ℂ :=
    fun r s => ((Y r)ᴴ * Y s) l m -
      (if r = s then if l = m then 1 else 0 else 0)
  have hT (l m : Fin c) : NativeFourKernel.compression X (T l m) = 0 := by
    rw [NativeFourKernel.compression, NativeRectangularBound.stackK_compression]
    exact NativeRectangularBound.block_kernel X Y hF hX l m
  have hJ : (Y 3)ᴴ * Y 3 = 1 := by
    ext l m
    have h := h33 (T l m) (hT l m)
    simpa [T, Matrix.one_apply] using sub_eq_zero.mp h
  have horth : (Y 3)ᴴ * (∑ i, v i • Y i) = 0 := by
    ext l m
    have h := hrow (T l m) (hT l m)
    rw [Matrix.mul_sum]
    simp_rw [Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simpa [T, v, Fin.sum_univ_four, mul_comm] using h
  exact ⟨hJ, v, hv, by simp [v], horth⟩
open private tensor_mix from D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound
open private normalize_rank_three rank_sum from
  D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree
open private kernel_columns from D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase

private theorem pivot_right_combination {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (v : Fin 4 → ℂ) (hv : v ≠ 0) (hv3 : v 3 = 0) :
    ∃ (A : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (B : Fin 4 → Matrix (Fin d) (Fin c) ℂ),
      (∑ i, kronecker (A i) (B i)) = (∑ i, kronecker (X i) (Y i)) ∧
      B 2 = ∑ i, v i • Y i ∧ B 3 = Y 3 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  have hk3 : k ≠ 3 := fun h => hk (h ▸ hv3)
  let p : Equiv.Perm (Fin 4) := Equiv.swap 2 k
  let L := fun i => X (p i)
  let R := fun i => Y (p i)
  let u := fun i => v (p i)
  let P := (1 : Matrix (Fin 4) (Fin 4) ℂ).updateRow 2 u
  have hrow : (∑ i, u i • (1 : Matrix (Fin 4) (Fin 4) ℂ) i) = u := by
    ext i
    simp [Matrix.one_apply, eq_comm]
  have hdet : P.det = v k := by
    dsimp [P]
    rw [← hrow, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]
    simp [u, p]
  let A := mix P.transpose⁻¹ L
  let B := mix P R
  refine ⟨A, B, ?_, ?_, ?_⟩
  · calc
      (∑ i, kronecker (A i) (B i)) = ∑ i, kronecker (L i) (R i) := by
        apply tensor_mix
        rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
          Matrix.nonsing_inv_mul _ (by rw [hdet]; exact IsUnit.mk0 _ hk)]
      _ = _ := Equiv.sum_comp p (fun j => kronecker (X j) (Y j))
  · change (∑ i, P 2 i • R i) = ∑ i, v i • Y i
    simp only [P, Matrix.updateRow_self]
    exact Equiv.sum_comp p (fun j => v j • Y j)
  · have h3 : p 3 = 3 := Equiv.swap_apply_of_ne_of_ne (by decide) hk3.symm
    change (∑ i, P 3 i • R i) = Y 3
    simpa [P, Matrix.updateRow_ne, Matrix.one_apply, R, h3]
open private reduce_right from D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound
open private neutral_plane_bound from D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeThreeRectangularBound
open private complex_block_annihilated from D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeCommonKernelBound
open private flat_mix from D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation

private theorem no_width_two {a b e d : ℕ} (hab : a < b) (he : 0 < e) (hde : d < 2 * e)
    (X : Fin 2 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 2 → Matrix (Fin d) (Fin e) ℂ)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) = 1) : False := by
  classical
  have one_term (A : Fin 1 → Matrix (Fin a) (Fin b) ℂ)
      (B : Fin 1 → Matrix (Fin d) (Fin e) ℂ)
      (h : (∑ i, kronecker (A i) (B i)) = ∑ i, kronecker (X i) (Y i)) : False := by
    rw [← h, Fin.sum_univ_one] at hF
    let W := kronecker (A 0) (B 0)
    have hW := column_rank W hF
    have hfac : W = kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (B 0) *
        kronecker (A 0) (1 : Matrix (Fin e) (Fin e) ℂ) := by
      simp only [W, Matrix.kronecker, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul, Matrix.mul_one]
    have hdim : b * e ≤ a * e := by
      rw [← hW, hfac]
      apply (Matrix.rank_mul_le_right _ _).trans
      simpa only [Fintype.card_prod, Fintype.card_fin] using
        (Matrix.rank_le_card_height (kronecker (A 0) (1 : Matrix (Fin e) (Fin e) ℂ)))
    exact (Nat.not_le_of_lt (Nat.mul_lt_mul_of_pos_right hab he)) hdim
  by_cases hX : LinearIndependent ℂ X
  · by_cases hY : LinearIndependent ℂ Y
    · obtain ⟨B, _, _, hEq, hGram, hInd⟩ := NativeRectangularBound.exact_whitening X Y hY he hF
      have hw := D5.S3.Quantum.Algebra.NativeTwoKernelBound.right_dimension_bound hab _ _
        (hInd hX) (by rw [hEq, hF]) hGram
      omega
    · obtain ⟨v, hrel, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hY
      obtain ⟨A, B, h⟩ := reduce_right (n := 1) X Y v i hi hrel
      exact one_term A B h
  · obtain ⟨v, hrel, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hX
    obtain ⟨A, B, h⟩ := reduce_left (n := 1) X Y v i hi hrel
    exact one_term A B h

private theorem isolated_right_gram {a b e d : ℕ} (hab : a < b) (hde : d < 2 * e)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 3 → Matrix (Fin d) (Fin e) ℂ)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) = 1)
    (hJ : (Y 2)ᴴ * Y 2 = 1) : LinearIndependent ℂ Y ∧
      (∀ i, ∃ z : ℂ, (Y 2)ᴴ * Y i = z • 1) := by
  classical
  have he : 0 < e := by omega
  have hX : LinearIndependent ℂ X := by
    by_contra h
    obtain ⟨v, hv, i, hi⟩ := Fintype.not_linearIndependent_iff.mp h
    obtain ⟨A, B, hEq⟩ := reduce_left (n := 2) X Y v i hi hv
    exact no_width_two hab he hde A B (by rw [hEq, hF])
  have hY : LinearIndependent ℂ Y := by
    by_contra h
    obtain ⟨v, hv, i, hi⟩ := Fintype.not_linearIndependent_iff.mp h
    obtain ⟨A, B, hEq⟩ := reduce_right (n := 2) X Y v i hi hv
    exact no_width_two hab he hde A B (by rw [hEq, hF])
  refine ⟨hY, ?_⟩
  obtain ⟨B, hB, _, hEq, hGram, hInd⟩ := NativeRectangularBound.exact_whitening X Y hY he hF
  let U := D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix B X
  let W := D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix B.transpose⁻¹ Y
  have hunit : (∑ i, kronecker (U i) (W i))ᴴ * (∑ i, kronecker (U i) (W i)) = 1 := by
    rw [show (∑ i, kronecker (U i) (W i)) = ∑ i, kronecker (X i) (Y i) from hEq, hF]
  have hUGram : (NativeRectangularBound.stackK U)ᴴ * NativeRectangularBound.stackK U = 1 := by
    rw [NativeRectangularBound.stackK_gram]
    exact hGram
  obtain ⟨v, hv, hcommon⟩ | ⟨L, hL, hneutral⟩ :=
    D5.S3.Quantum.Algebra.NativeThreeKernelGeometry.native_three_compression_kernel_geometry
      a b hab U (hInd hX)
      (D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation.gram_identity_injective _ hUGram)
  · let Z : Matrix (Fin d) (Fin e) ℂ := ∑ i, v i • W i
    have hWZ (r : Fin 3) : (W r)ᴴ * Z = v r • 1 := by
      ext l m
      have hz := congrFun (complex_block_annihilated U W hunit hGram v hcommon l m) r
      have ht : ∑ s : Fin 3, ((W r)ᴴ * W s) l m * v s =
          ((1 : Matrix (Fin e) (Fin e) ℂ) l m) * v r := by
        change (∑ s : Fin 3, (((W r)ᴴ * W s) l m -
          (if r = s then if l = m then 1 else 0 else 0)) * v s) = 0 at hz
        simp_rw [sub_mul, Finset.sum_sub_distrib] at hz
        simpa [Matrix.one_apply, ite_mul] using sub_eq_zero.mp hz
      simpa [Z, Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, mul_comm] using ht
    let ν : ℂ := star v ⬝ᵥ v
    have hν : ν ≠ 0 := fun h => hv (dotProduct_star_self_eq_zero.mp h)
    have hZZ : Zᴴ * Z = ν • 1 := by
      simp only [Z, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
        Matrix.smul_mul, hWZ, smul_smul, ← Finset.sum_smul, ν, dotProduct]
      rfl
    have hFlat : D5.S3.Quantum.Algebra.NativeCoefficientWhitening.flat W * B =
        D5.S3.Quantum.Algebra.NativeCoefficientWhitening.flat Y := by
      dsimp only [W]
      rw [flat_mix, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hB),
        Matrix.mul_one]
    have hback (r : Fin 3) : Y r = ∑ s, B s r • W s := by
      ext i j
      have h := congrFun (congrFun hFlat (i, j)) r
      simpa [D5.S3.Quantum.Algebra.NativeCoefficientWhitening.flat,
        Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using h.symm
    have hYZ (r : Fin 3) : ∃ z : ℂ, (Y r)ᴴ * Z = z • 1 := by
      refine ⟨∑ s, star (B s r) * v s, ?_⟩
      rw [hback]
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
        Matrix.smul_mul, hWZ, smul_smul, ← Finset.sum_smul]
    obtain ⟨α, hα⟩ := hYZ 2
    let τ := star α / ν
    let D := Y 2 - τ • Z
    have hZD : Zᴴ * D = 0 := by
      have hZJ : Zᴴ * Y 2 = star α • 1 := by
        simpa using congrArg Matrix.conjTranspose hα
      simp [D, hZJ, Matrix.mul_sub, Matrix.mul_smul, hZZ, smul_smul, τ, hν]
    have hDD : Dᴴ * D = (1 - τ * α) • 1 := by
      calc
        Dᴴ * D = (Y 2)ᴴ * D := by
          simp [D, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.sub_mul,
            Matrix.smul_mul, show Zᴴ * (Y 2 - τ • Z) = 0 from hZD]
        _ = (1 - τ * α) • 1 := by
          simp [D, Matrix.mul_sub, Matrix.mul_smul, hJ, hα, smul_smul, sub_smul, mul_comm]
    have hrank {A : Matrix (Fin d) (Fin e) ℂ} {z : ℂ} (hz : z ≠ 0)
        (hA : Aᴴ * A = z • 1) : A.rank = e := by
      rw [← Matrix.rank_conjTranspose_mul_self A, hA, Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hz),
        Matrix.rank_one, Fintype.card_fin]
    have hz : 1 - τ * α = 0 := by
      by_contra h
      have hp := Matrix.rank_add_rank_le_card_of_mul_eq_zero hZD
      rw [Matrix.rank_conjTranspose, hrank hν hZZ, hrank h hDD, Fintype.card_fin] at hp
      omega
    have hD : D = 0 :=
      Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa only [hz, zero_smul] using hDD)
    have hJZ : Y 2 = τ • Z := sub_eq_zero.mp hD
    intro i
    obtain ⟨z, hz⟩ := hYZ i
    have hz' : Zᴴ * Y i = star z • 1 := by simpa using congrArg Matrix.conjTranspose hz
    exact ⟨star τ * star z, by rw [hJZ, Matrix.conjTranspose_smul, Matrix.smul_mul, hz', smul_smul]⟩
  · have := neutral_plane_bound U W hunit hGram L hL hneutral
    omega

private theorem residual_kernel {a b e d : ℕ}
    (A B : Matrix (Fin a) (Fin b) ℂ) (R S D : Matrix (Fin d) (Fin e) ℂ)
    (P : Matrix (Fin b) (Fin b) ℂ) (hde : d < 2 * e)
    (hDD : Dᴴ * D = 1) (hR : Dᴴ * R = 0) (hS : Dᴴ * S = 0)
    (hF : (kronecker A R + kronecker B S)ᴴ * (kronecker A R + kronecker B S) =
      kronecker P (1 : Matrix (Fin e) (Fin e) ℂ))
    {s t : ℂ} (hst : s ≠ 0 ∨ t ≠ 0) {x : Fin b → ℂ}
    (hx : (s • A + t • B) *ᵥ x = 0) : P *ᵥ x = 0 := by
  classical
  let F := kronecker A R + kronecker B S
  let product (v : Fin b → ℂ) (w : Fin e → ℂ) := (Matrix.vecMulVec w v).vec
  have tensor_apply {m n : ℕ} (M : Matrix (Fin m) (Fin b) ℂ)
      (N : Matrix (Fin n) (Fin e) ℂ)
      (w : Fin e → ℂ) :
      kronecker M N *ᵥ product x w =
        (Matrix.vecMulVec (N *ᵥ w) (M *ᵥ x)).vec := by
    dsimp only [product]
    rw [Matrix.kronecker, Matrix.kronecker_mulVec_vec, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  have kernel_nonzero (C : Matrix (Fin d) (Fin e) ℂ) (hC : Dᴴ * C = 0) :
      ∃ y : Fin e → ℂ, y ≠ 0 ∧ C *ᵥ y = 0 := by
    have hd : Dᴴ.rank = e := by
      rw [Matrix.rank_conjTranspose, ← Matrix.rank_conjTranspose_mul_self D, hDD,
        Matrix.rank_one, Fintype.card_fin]
    have hc := Matrix.rank_add_rank_le_card_of_mul_eq_zero hC
    rw [hd, Fintype.card_fin] at hc
    have hh : ¬ Function.Injective C.mulVecLin := by
      intro hv
      have hr : C.rank = e := by
        rw [Matrix.rank, LinearMap.finrank_range_of_inj hv,
          Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      omega
    obtain ⟨y, z, hyz, hC⟩ := Function.not_injective_iff.mp hh
    refine ⟨y-z, sub_ne_zero.mpr hC, ?_⟩
    change C.mulVecLin (y-z) = 0
    rw [map_sub, hyz, sub_self]
  have hzero : ∃ y : Fin e → ℂ, y ≠ 0 ∧ F *ᵥ product x y = 0 := by
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec] at hx
    by_cases hs : s = 0
    · have hB : B *ᵥ x = 0 := by
        apply (smul_eq_zero.mp _).resolve_left (hst.resolve_left (not_not_intro hs))
        simpa [hs] using hx
      obtain ⟨y, hy, hR⟩ := kernel_nonzero R hR
      refine ⟨y, hy, ?_⟩
      change (kronecker A R + kronecker B S) *ᵥ product x y = 0
      rw [Matrix.add_mulVec, tensor_apply, tensor_apply, hR, hB]
      ext ⟨i, j⟩
      simp [Matrix.vec, Matrix.vecMulVec_apply]
    · let z := -t / s
      have hA : A *ᵥ x = z • (B *ᵥ x) := by
        apply (smul_right_injective (Fin a → ℂ) hs)
        change s • (A *ᵥ x) = s • (z • (B *ᵥ x))
        rw [smul_smul, show s * z = -t by dsimp [z]; field_simp, neg_smul]
        exact eq_neg_of_add_eq_zero_left hx
      obtain ⟨y, hy, hY⟩ := kernel_nonzero (z • R + S)
        (by simp [Matrix.mul_add, Matrix.mul_smul, hR, hS])
      refine ⟨y, hy, ?_⟩
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec] at hY
      dsimp only [F]
      rw [Matrix.add_mulVec, tensor_apply, tensor_apply, hA]
      ext ⟨i,j⟩
      simp only [Matrix.vec, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
        Pi.add_apply, Pi.zero_apply]
      have h := congrFun hY j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      linear_combination (B *ᵥ x) i * h
  obtain ⟨y, hy, hzero⟩ := hzero
  have heq : kronecker P (1 : Matrix (Fin e) (Fin e) ℂ) *ᵥ product x y = 0 := by
    rw [← hF, ← Matrix.mulVec_mulVec, show F *ᵥ product x y = 0 from hzero,
      Matrix.mulVec_zero]
  rw [tensor_apply, Matrix.one_mulVec] at heq
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  ext i
  have h := congrFun heq (i, j)
  exact (mul_eq_zero.mp (show y j * (P *ᵥ x) i = 0 from h)).resolve_left hj

private theorem rank_sum_product {m n p q : ℕ}
    (A B : Matrix (Fin m × Fin n) (Fin p × Fin q) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  let r : Fin (m * n) ≃ Fin m × Fin n := finProdFinEquiv.symm
  let c : Fin (p * q) ≃ Fin p × Fin q := finProdFinEquiv.symm
  have h := rank_sum (A.submatrix r c) (B.submatrix r c)
  change ((A + B).submatrix r c).rank ≤ (A.submatrix r c).rank + (B.submatrix r c).rank at h
  simpa only [Matrix.rank_submatrix] using h

private theorem projected_width_three {a b c d q : ℕ}
    (F : Matrix (Fin a × Fin d) (Fin b × Fin c) ℂ)
    (X : Matrix (Fin a) (Fin b) ℂ) (J : Matrix (Fin d) (Fin c) ℂ)
    (Z : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (C : Matrix (Fin d) (Fin q) ℂ)
    (hF : Fᴴ * F = 1)
    (hdecomp : F = kronecker X J + ∑ i, kronecker (Z i) (Y i))
    (hX : X * Xᴴ = 1) (hZ : ∀ i, Z i * Xᴴ = 0)
    (hC : Cᴴ * C = 1) (hCJ : Cᴴ * J = 0) :
    a * q ≤ (a * d - b * c) + 3 * ((b - a) * q) := by
  classical
  let CS := kronecker (1 : Matrix (Fin a) (Fin a) ℂ) C
  let W := CSᴴ * F
  let V := CSᴴ * (1 - F * Fᴴ) * CS
  let D := (1 : Matrix (Fin b) (Fin b) ℂ) - Xᴴ * X
  have hCS : CSᴴ * CS = 1 := by
    simp only [CS, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hC,
      Matrix.one_kronecker_one]
  have hsum : W * Wᴴ + V = 1 := by
    simp only [W, V, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [← hCS]
    abel
  have hdefect := row_defect_rank F hF
  have hv : V.rank ≤ (1 - F * Fᴴ).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hd : D.rank ≤ b - a := by
    have hDX : D * Xᴴ = 0 := by
      simp [D, Matrix.sub_mul, Matrix.mul_assoc, hX]
    have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero hDX
    have hx : Xᴴ.rank = a := by
      rw [← Matrix.rank_conjTranspose_mul_self Xᴴ, Matrix.conjTranspose_conjTranspose,
        hX, Matrix.rank_one, Fintype.card_fin]
    rw [hx, Fintype.card_fin] at h
    omega
  have hW : W = ∑ i, Matrix.kronecker (Z i) (Cᴴ * Y i) := by
    dsimp only [W]
    rw [hdecomp]
    simp only [CS, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Matrix.mul_add, Matrix.mul_sum,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hCJ, Matrix.kronecker_zero, zero_add]
  have hr (i : Fin 3) : (kronecker (Z i) (Cᴴ * Y i)).rank ≤ (b - a) * q := by
    have hZd : Z i * D = Z i := by
      simp [D, Matrix.mul_sub, ← Matrix.mul_assoc, hZ i]
    have hfac : kronecker (Z i) (Cᴴ * Y i) =
        kronecker (Z i) (1 : Matrix (Fin q) (Fin q) ℂ) *
          kronecker D (1 : Matrix (Fin q) (Fin q) ℂ) *
          kronecker (1 : Matrix (Fin b) (Fin b) ℂ) (Cᴴ * Y i) := by
      simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, hZd,
        Matrix.mul_one, Matrix.one_mul]
    rw [hfac]
    refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
    rw [rank_kronecker_one_general]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left q hd
  have hWr : W.rank ≤ 3 * ((b - a) * q) := by
    let K (i : Fin 3) := kronecker (Z i) (Cᴴ * Y i)
    rw [hW]
    change (∑ i, K i).rank ≤ _
    rw [Fin.sum_univ_three]
    have h01 := rank_sum_product (K 0) (K 1)
    have h012 := rank_sum_product (K 0 + K 1) (K 2)
    have h0 : (K 0).rank ≤ (b - a) * q := hr 0
    have h1 : (K 1).rank ≤ (b - a) * q := hr 1
    have h2 : (K 2).rank ≤ (b - a) * q := hr 2
    omega
  have hfinal := rank_sum_product (W * Wᴴ) V
  rw [hsum, Matrix.rank_one, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Matrix.rank_self_mul_conjTranspose] at hfinal
  omega

private theorem small_defect_of_isolated_slice {a b c d e : ℕ}
    (X A B Z : Matrix (Fin a) (Fin b) ℂ) (J R S V : Matrix (Fin d) (Fin c) ℂ)
    (E : Matrix (Fin c) (Fin e) ℂ)
    (hJJ : Jᴴ * J = 1) (hJV : Jᴴ * V = 0) (hE : Eᴴ * E = 1) (hVE : V * E = 0)
    (hR : (J * E)ᴴ * (R * E) = 0) (hS : (J * E)ᴴ * (S * E) = 0)
    (hRight : ∀ s t : ℂ, s • (R * E) + t • (S * E) = 0 → s = 0 ∧ t = 0)
    (hab : a < b) (hde : d < 2 * e) (hsmall : a * d - b * c < e)
    (hF : let F := kronecker X J + kronecker A R + kronecker B S + kronecker Z V
      Fᴴ * F = 1) : 4 * c ≤ 3 * d := by
  classical
  let F := kronecker X J + kronecker A R + kronecker B S + kronecker Z V
  change Fᴴ * F = 1 at hF
  let P : Matrix (Fin b) (Fin b) ℂ := 1 - Xᴴ * X
  let D := J * E
  let L := kronecker X D
  let H := kronecker A (R * E) + kronecker B (S * E)
  let CE := kronecker (1 : Matrix (Fin b) (Fin b) ℂ) E
  have hDD : Dᴴ * D = 1 := by
    calc
      Dᴴ * D = Eᴴ * (Jᴴ * J) * E := by simp only [D, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, hE]
  have hCE : CEᴴ * CE = 1 := by
    simp only [CE, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, hE, Matrix.one_kronecker_one]
  have hFE : F * CE = L + H := by
    simp only [F, CE, L, H, D, Matrix.add_mul, Matrix.kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hVE, Matrix.kronecker_zero, add_zero, add_assoc]
  have hLH : Lᴴ * H = 0 := by
    simp only [L, H, Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.mul_add,
      ← Matrix.mul_kronecker_mul, show Dᴴ * (R * E) = 0 from hR,
      show Dᴴ * (S * E) = 0 from hS, Matrix.kronecker_zero, add_zero]
  have hHL : Hᴴ * L = 0 := by simpa using congrArg Matrix.conjTranspose hLH
  have hH : Hᴴ * H = kronecker P (1 : Matrix (Fin e) (Fin e) ℂ) := by
    have h : (F * CE)ᴴ * (F * CE) = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ F,
        hF, Matrix.one_mul, hCE]
    rw [hFE] at h
    have hLL : Lᴴ * L = kronecker (Xᴴ * X) (1 : Matrix (Fin e) (Fin e) ℂ) := by
      simp only [L, Matrix.kronecker, Matrix.conjTranspose_kronecker,
        ← Matrix.mul_kronecker_mul, hDD]
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add Lᴴ L H,
      Matrix.mul_add Hᴴ L H, hLH, hHL, add_zero, zero_add, hLL] at h
    change Hᴴ * H = kronecker (1 - Xᴴ * X) (1 : Matrix (Fin e) (Fin e) ℂ)
    rw [sub_kron, show kronecker (1 : Matrix (Fin b) (Fin b) ℂ)
      (1 : Matrix (Fin e) (Fin e) ℂ) = 1 from Matrix.one_kronecker_one]
    rw [← h]
    abel
  have kill {k : ℕ} (M : Matrix (Fin b) (Fin k) ℂ) (hM : P * M = 0) :
      A * M = 0 ∧ B * M = 0 := by
    have hK : H * kronecker M (1 : Matrix (Fin e) (Fin e) ℂ) = 0 := by
      apply (Matrix.conjTranspose_mul_self_mul_eq_zero H _).mp
      rw [hH]
      simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, hM,
        Matrix.one_mul, Matrix.zero_kronecker]
    have hK' : kronecker (A * M) (R * E) + kronecker (B * M) (S * E) = 0 := by
      simpa only [H, Matrix.kronecker, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one] using hK
    have hcoef (i : Fin a) (j : Fin k) : (A * M) i j = 0 ∧ (B * M) i j = 0 := by
      apply hRight
      ext l m
      have hh := congrArg (fun W : Matrix (Fin a × Fin d) (Fin k × Fin e) ℂ =>
        W (i, l) (j, m)) hK'
      simpa only [Matrix.add_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using hh
    exact ⟨Matrix.ext fun i j => (hcoef i j).1, Matrix.ext fun i j => (hcoef i j).2⟩
  let l := b - P.rank
  obtain ⟨C, hCC, hPC, _⟩ := kernel_columns P
  have hCP : Cᴴ * P = 0 := by
    have hPH : Pᴴ = P := by simp [P]
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero, hPH] using
      congrArg Matrix.conjTranspose hPC
  have hCX : Cᴴ * Xᴴ * X = Cᴴ := by
    have h := hCP
    dsimp only [P] at h
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, sub_eq_zero] at h
    exact h.symm
  have hLC : (X * C)ᴴ * (X * C) = 1 := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, hCX, hCC]
  let CL := kronecker C E
  have hFL : F * CL = kronecker (X * C) D := by
    obtain ⟨hA, hB⟩ := kill C hPC
    simp only [F, CL, D, Matrix.kronecker, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
      hA, hB, hVE, Matrix.zero_kronecker, Matrix.kronecker_zero, add_zero]
  have hcols : (kronecker (X * C) D)ᴴ * F = CLᴴ := by
    rw [← hFL, Matrix.conjTranspose_mul, Matrix.mul_assoc, hF, Matrix.mul_one]
  have hDV : Dᴴ * V = 0 := by
    simp only [D, Matrix.conjTranspose_mul, Matrix.mul_assoc, hJV, Matrix.mul_zero]
  have hDJ : Dᴴ * J = Eᴴ := by
    simp only [D, Matrix.conjTranspose_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hcross :
      kronecker ((X * C)ᴴ * A) (Dᴴ * R) + kronecker ((X * C)ᴴ * B) (Dᴴ * S) = 0 := by
    have h := hcols
    simp only [F, CL, Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.mul_add,
      ← Matrix.mul_kronecker_mul, hDV, Matrix.kronecker_zero, add_zero,
      Matrix.conjTranspose_mul X C, hCX, hDJ] at h
    apply add_left_cancel (a := kronecker Cᴴ Eᴴ)
    simpa only [Matrix.conjTranspose_mul, Matrix.kronecker, add_assoc, add_zero] using h
  have hCrossZero : Dᴴ * R = 0 ∧ Dᴴ * S = 0 := by
    have hz (i : Fin e) (j : Fin c) : (Dᴴ * R) i j = 0 ∧ (Dᴴ * S) i j = 0 := by
      let s := (Dᴴ * R) i j
      let t := (Dᴴ * S) i j
      let M := s • A + t • B
      have hM : (X * C)ᴴ * M = 0 := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
        ext u v
        have hh := congrArg (fun W : Matrix (Fin l × Fin e) (Fin b × Fin c) ℂ =>
          W (u, i) (v, j)) hcross
        simpa [s, t, Matrix.add_apply, Matrix.smul_apply, Matrix.kronecker,
          Matrix.kroneckerMap_apply, smul_eq_mul, mul_comm] using hh
      by_contra hst
      have hst' : s ≠ 0 ∨ t ≠ 0 := by
        by_cases hs : s = 0
        · exact Or.inr (fun ht => hst ⟨hs, ht⟩)
        · exact Or.inl hs
      have hker : LinearMap.ker M.mulVecLin ≤ LinearMap.ker P.mulVecLin := by
        intro x hx
        exact residual_kernel A B (R * E) (S * E) D P hde hDD hR hS hH hst' hx
      have hK := Submodule.finrank_mono hker
      have hp := P.mulVecLin.finrank_range_add_finrank_ker
      have hm := M.mulVecLin.finrank_range_add_finrank_ker
      change P.rank + finrank ℂ (LinearMap.ker P.mulVecLin) = _ at hp
      change M.rank + finrank ℂ (LinearMap.ker M.mulVecLin) = _ at hm
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hp hm
      have hdim := Matrix.rank_add_rank_le_card_of_mul_eq_zero hM
      have hLCrank : (X * C)ᴴ.rank = l := by
        rw [Matrix.rank_conjTranspose, ← Matrix.rank_conjTranspose_mul_self (X * C),
          hLC, Matrix.rank_one, Fintype.card_fin]
      rw [hLCrank, Fintype.card_fin] at hdim
      dsimp [l] at hdim
      omega
    exact ⟨Matrix.ext fun i j => (hz i j).1, Matrix.ext fun i j => (hz i j).2⟩
  let Q := kronecker (1 : Matrix (Fin a) (Fin a) ℂ) D
  have hQQ : Qᴴ * Q = 1 := by
    simp only [Q, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      hDD, Matrix.one_kronecker_one]
  have hQF : Qᴴ * F = kronecker X Eᴴ := by
    simp only [Q, F, Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      Matrix.mul_add, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      hDJ, hDV, hCrossZero.1, hCrossZero.2, Matrix.kronecker_zero, add_zero]
  have hdef : Qᴴ * (1 - F * Fᴴ) * Q =
      kronecker (1 - X * Xᴴ) (1 : Matrix (Fin e) (Fin e) ℂ) := by
    calc
      Qᴴ * (1 - F * Fᴴ) * Q = Qᴴ * Q - (Qᴴ * F) * (Qᴴ * F)ᴴ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by
        rw [hQQ, hQF]
        have hXEE : kronecker X Eᴴ * (kronecker X Eᴴ)ᴴ =
            kronecker (X * Xᴴ) (1 : Matrix (Fin e) (Fin e) ℂ) := by
          simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
            Matrix.conjTranspose_conjTranspose, ← Matrix.mul_kronecker_mul, hE]
        rw [hXEE, sub_kron, show kronecker (1 : Matrix (Fin a) (Fin a) ℂ)
          (1 : Matrix (Fin e) (Fin e) ℂ) = 1 from Matrix.one_kronecker_one]
  have hXX := (small_defect_compression F hF X D hdef).2 hsmall
  have hPX : P * Xᴴ = 0 := by simp [P, Matrix.sub_mul, Matrix.mul_assoc, hXX]
  obtain ⟨hAX, hBX⟩ := kill Xᴴ hPX
  let Z' := if V = 0 then 0 else Z
  have hZ' : kronecker Z' V = kronecker Z V := by
    by_cases h : V = 0 <;> simp [Z', h]
  have hZX : Z' * Xᴴ = 0 := by
    by_cases hV : V = 0
    · simp [Z', hV]
    have h0 : (F * kronecker Xᴴ (1 : Matrix (Fin c) (Fin c) ℂ))ᴴ *
        (F * kronecker Xᴴ (1 : Matrix (Fin c) (Fin c) ℂ)) = 1 := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ F,
        hF, Matrix.one_mul, Matrix.kronecker, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, hXX, Matrix.one_kronecker_one]
    let Y := kronecker (1 : Matrix (Fin a) (Fin a) ℂ) J
    let W := kronecker (Z * Xᴴ) V
    have hFW : F * kronecker Xᴴ (1 : Matrix (Fin c) (Fin c) ℂ) = Y + W := by
      simp only [F, Y, W, Matrix.kronecker, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one, hXX, hAX, hBX, Matrix.zero_kronecker, add_zero]
    have hYW : Yᴴ * W = 0 := by
      simp only [Y, W, Matrix.kronecker, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, hJV, Matrix.kronecker_zero]
    have hWY : Wᴴ * Y = 0 := by simpa using congrArg Matrix.conjTranspose hYW
    have hYY : Yᴴ * Y = 1 := by
      simp only [Y, Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul, hJJ, Matrix.one_kronecker_one]
    have hW : W = 0 := by
      apply Matrix.conjTranspose_mul_self_eq_zero.mp
      rw [hFW] at h0
      simpa only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        hYW, hWY, hYY, add_zero, zero_add, add_eq_left] using h0
    obtain ⟨i, j, hij⟩ : ∃ i j, V i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hV (Matrix.ext h)
    have hZ : Z * Xᴴ = 0 := by
      ext u v
      have h := congrArg (fun M : Matrix (Fin a × Fin d) (Fin a × Fin c) ℂ =>
        M (u, i) (v, j)) hW
      exact (mul_eq_zero.mp (show (Z * Xᴴ) u v * V i j = 0 from h)).resolve_right hij
    simpa only [Z', if_neg hV] using hZ
  have hJrank : Jᴴ.rank = c := by
    rw [Matrix.rank_conjTranspose, ← Matrix.rank_conjTranspose_mul_self J, hJJ,
      Matrix.rank_one, Fintype.card_fin]
  have hcd : c ≤ d := by
    simpa only [hJrank, Fintype.card_fin] using Jᴴ.rank_le_card_width
  obtain ⟨K, hKK, hJK⟩ :
      ∃ K : Matrix (Fin d) (Fin (d - c)) ℂ, Kᴴ * K = 1 ∧ Jᴴ * K = 0 := by
    obtain ⟨K, hKK, hJK, _⟩ := kernel_columns Jᴴ
    rw [show d - c = d - Jᴴ.rank by rw [hJrank]]
    exact ⟨K, hKK, hJK⟩
  have hKJ : Kᴴ * J = 0 := by simpa using congrArg Matrix.conjTranspose hJK
  let U : Fin 3 → Matrix (Fin a) (Fin b) ℂ := ![A, B, Z']
  let W : Fin 3 → Matrix (Fin d) (Fin c) ℂ := ![R, S, V]
  have hUW : F = kronecker X J + ∑ i, kronecker (U i) (W i) := by
    rw [Fin.sum_univ_three]
    change F = kronecker X J + (kronecker A R + kronecker B S + kronecker Z' V)
    rw [hZ']
    simp only [F, add_assoc]
  have hUX (i : Fin 3) : U i * Xᴴ = 0 := by
    fin_cases i <;> simp [U, hAX, hBX, hZX]
  have hbound := projected_width_three F X J U W K hF hUW hXX hUX hKK hKJ
  have hdim : b * c ≤ a * d := by
    simpa only [column_rank F hF, Fintype.card_prod, Fintype.card_fin] using F.rank_le_card_height
  have h₁ : a * (d - c) + a * c = a * d := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hcd]
  have h₂ : (b - a) * c + a * c = b * c := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hab.le]
  have hp : (b - a) * c ≤ (b - a) * (3 * (d - c)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (b - a) 3, Nat.mul_assoc]
    omega
  have := Nat.le_of_mul_le_mul_left hp (Nat.sub_pos_of_lt hab)
  omega

private theorem bounds_of_orthogonal_combination {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) = 1)
    (hab : a < b) (v : Fin 4 → ℂ) (hv : v ≠ 0) (hv3 : v 3 = 0)
    (hJ : (Y 3)ᴴ * Y 3 = 1) (hV : (Y 3)ᴴ * (∑ i, v i • Y i) = 0) :
    6 * c ≤ 5 * d ∧ (a * d - b * c < 2 * c - d → 4 * c ≤ 3 * d) := by
  classical
  obtain ⟨A, B, hAB, h₂, h₃⟩ := pivot_right_combination X Y v hv hv3
  let J := B 3
  let V := B 2
  have hJJ : Jᴴ * J = 1 := by simpa only [J, h₃] using hJ
  have hJV : Jᴴ * V = 0 := by simpa only [J, V, h₂, h₃] using hV
  have hJrank : Jᴴ.rank = c := by
    rw [Matrix.rank_conjTranspose, ← Matrix.rank_conjTranspose_mul_self J, hJJ,
      Matrix.rank_one, Fintype.card_fin]
  have hVr := Matrix.rank_add_rank_le_card_of_mul_eq_zero hJV
  rw [hJrank, Fintype.card_fin] at hVr
  let e := c - V.rank
  obtain ⟨E, hEE, hVE, _⟩ := kernel_columns V
  let C := kronecker (1 : Matrix (Fin b) (Fin b) ℂ) E
  let M : Fin 3 → Matrix (Fin a) (Fin b) ℂ := ![A 0, A 1, A 3]
  let N : Fin 3 → Matrix (Fin d) (Fin e) ℂ := ![B 0 * E, B 1 * E, J * E]
  have hC : Cᴴ * C = 1 := by
    simp only [C, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      hEE, Matrix.one_kronecker_one]
  have hsum : ∑ i, kronecker (M i) (N i) = (∑ i, kronecker (A i) (B i)) * C := by
    simp [M, N, C, J, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.kronecker,
      Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      show B 2 * E = 0 from hVE, Matrix.kronecker_zero, add_assoc]
  have hMN : (∑ i, kronecker (M i) (N i))ᴴ * (∑ i, kronecker (M i) (N i)) = 1 := by
    rw [hsum, hAB, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ _ C, hF, Matrix.one_mul, hC]
  have h₆ := NativeThreeRectangularBound.native_three_rectangular_bound M N 1 (by norm_num) hab
    (by simpa using hMN)
  refine ⟨by dsimp [e] at h₆; omega, ?_⟩
  intro hsmall
  by_contra h
  have hde : d < 2 * e := by dsimp [e]; omega
  have hse : a * d - b * c < e := by dsimp [e]; omega
  have hD : (J * E)ᴴ * (J * E) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J E,
      hJJ, Matrix.one_mul, hEE]
  obtain ⟨hNI, hi⟩ := isolated_right_gram hab hde M N hMN (by simpa [N] using hD)
  obtain ⟨α, hα⟩ := hi 0
  obtain ⟨β, hβ⟩ := hi 1
  let L := A 3 + α • A 0 + β • A 1
  let R := B 0 - α • J
  let S := B 1 - β • J
  have hRE : R * E = N 0 - α • N 2 := by simp [R, N, Matrix.sub_mul, Matrix.smul_mul]
  have hSE : S * E = N 1 - β • N 2 := by simp [S, N, Matrix.sub_mul, Matrix.smul_mul]
  have hR : (J * E)ᴴ * (R * E) = 0 := by
    rw [hRE, Matrix.mul_sub, Matrix.mul_smul, show J * E = N 2 from rfl, hα,
      show (N 2)ᴴ * N 2 = 1 from hD, sub_self]
  have hS : (J * E)ᴴ * (S * E) = 0 := by
    rw [hSE, Matrix.mul_sub, Matrix.mul_smul, show J * E = N 2 from rfl, hβ,
      show (N 2)ᴴ * N 2 = 1 from hD, sub_self]
  have hindep (s t : ℂ) (hrel : s • (R * E) + t • (S * E) = 0) : s = 0 ∧ t = 0 := by
    let f : Fin 3 → ℂ := ![s, t, -(s * α + t * β)]
    have hf : ∑ i, f i • N i = 0 := by
      rw [Fin.sum_univ_three]
      change s • N 0 + t • N 1 + (-(s * α + t * β)) • N 2 = 0
      rw [hRE, hSE] at hrel
      convert hrel using 1
      simp only [smul_sub, smul_smul, neg_smul, add_smul]
      abel
    have hz := Fintype.linearIndependent_iff.mp hNI f hf
    exact ⟨hz 0, hz 1⟩
  have hpres : kronecker L J + kronecker (A 0) R + kronecker (A 1) S +
      kronecker (A 2) V = ∑ i, kronecker (X i) (Y i) := by
    rw [← hAB, Fin.sum_univ_four]
    dsimp only [L, R, S, J, V]
    rw [kron_sub, kron_sub]
    simp only [Matrix.kronecker, Matrix.add_kronecker, Matrix.smul_kronecker,
      Matrix.kronecker_smul]
    abel
  exact h (small_defect_of_isolated_slice L (A 0) (A 1) (A 2) J R S V E
    hJJ hJV hEE hVE hR hS hindep hab hde hse (by dsimp only; rw [hpres, hF]))
open private diagonal_energy from D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel

private theorem bounds_of_ordered_diagonal_compression {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hab : a < b)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ *
      (∑ i, kronecker (X i) (Y i)) = 1)
    (hX : ∑ i, (X i)ᴴ * X i = 1)
    (r s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hdiag : NativeFourKernel.compression X
      (diagonal (fun i => ((![(r : ℂ), -(s : ℂ), -(t : ℂ), 0]) i))) = 0) :
    6 * c ≤ 5 * d ∧ (a * d - b * c < 2 * c - d → 4 * c ≤ 3 * d) := by
  have hker : ∀ x : Fin b → ℂ, X 0 *ᵥ x = 0 →
      X 1 *ᵥ x = 0 ∧ X 2 *ᵥ x = 0 := by
    intro x hx
    have hdiag' : (fun i : Fin 4 => (((![r, -s, -t, 0] : Fin 4 → ℝ) i) : ℂ)) =
        ![(r : ℂ), -(s : ℂ), -(t : ℂ), 0] := by
      funext i
      fin_cases i <;> simp
    have h := diagonal_energy X ![r, -s, -t, 0] x (by
      rw [hdiag']
      exact hdiag)
    simp [Fin.sum_univ_four, hx] at h
    have hpos1 : 0 ≤ (s : ℂ) * (star (X 1 *ᵥ x) ⬝ᵥ (X 1 *ᵥ x)) :=
      mul_nonneg (by exact_mod_cast hs.le) (dotProduct_star_self_nonneg _)
    have hpos2 : 0 ≤ (t : ℂ) * (star (X 2 *ᵥ x) ⬝ᵥ (X 2 *ᵥ x)) :=
      mul_nonneg (by exact_mod_cast ht.le) (dotProduct_star_self_nonneg _)
    have he : (s : ℂ) * (star (X 1 *ᵥ x) ⬝ᵥ (X 1 *ᵥ x)) +
        (t : ℂ) * (star (X 2 *ᵥ x) ⬝ᵥ (X 2 *ᵥ x)) = 0 := by
      linear_combination -h
    obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg hpos1 hpos2).mp he
    exact ⟨dotProduct_star_self_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left
        (Complex.ofReal_ne_zero.mpr hs.ne')),
      dotProduct_star_self_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left
        (Complex.ofReal_ne_zero.mpr ht.ne'))⟩
  obtain ⟨hJ, v, hv, hv3, horth⟩ :=
    orthogonal_combination_of_one_direction_kernel X Y hab hF hX hker
  exact bounds_of_orthogonal_combination X Y hF hab v hv hv3 hJ horth

private theorem bounds_of_diagonal_compression {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ)
    (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hab : a < b)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ *
      (∑ i, kronecker (X i) (Y i)) = 1)
    (hX : ∑ i, (X i)ᴴ * X i = 1)
    (e : Fin 4 → ℝ)
    (hdiag : NativeFourKernel.compression X (diagonal (fun i => (e i : ℂ))) = 0)
    (hrank : (diagonal (fun i => (e i : ℂ))).rank = 3) :
    6 * c ≤ 5 * d ∧ (a * d - b * c < 2 * c - d → 4 * c ≤ 3 * d) := by
  classical
  have hsum : (∑ i, (e i : ℂ) • ((X i)ᴴ * X i)) = 0 := by
    simpa only [NativeFourKernel.compression, NativeRectangularBound.stackK_compression,
      Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true] using hdiag
  have hneg : (∑ i, ((-e i : ℝ) : ℂ) • ((X i)ᴴ * X i)) = 0 := by
    simp only [Complex.ofReal_neg, neg_smul, Finset.sum_neg_distrib, hsum, neg_zero]
  have hcount : Fintype.card {i : Fin 4 // e i ≠ 0} = 3 := by
    simpa only [Matrix.rank_diagonal, ne_eq, Complex.ofReal_eq_zero] using hrank
  have hzeroCount : Fintype.card {i : Fin 4 // e i = 0} = 1 := by
    simpa [hcount] using Fintype.card_subtype_compl (fun i : Fin 4 => e i ≠ 0)
  haveI : Subsingleton {i : Fin 4 // e i = 0} :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hn : Nonempty {i : Fin 4 // e i = 0} :=
    Fintype.card_pos_iff.mp (by omega)
  obtain ⟨⟨k, hk⟩⟩ := hn
  let p0 : Equiv.Perm (Fin 4) := Equiv.swap 3 k
  have hlast : e (p0 3) = 0 := by simpa [p0] using hk
  have hfirst (i : Fin 4) (hi : i ≠ 3) : e (p0 i) ≠ 0 := by
    intro hz
    have heq : (⟨p0 i, hz⟩ : {j : Fin 4 // e j = 0}) = ⟨p0 3, hlast⟩ :=
      Subsingleton.elim _ _
    exact hi (p0.injective (congrArg Subtype.val heq))
  have ordered (f : Fin 4 → ℝ)
      (hf : (∑ i, (f i : ℂ) • ((X i)ᴴ * X i)) = 0)
      (p : Equiv.Perm (Fin 4)) (h3 : f (p 3) = 0)
      (h1 : f (p 1) < 0) (h2 : f (p 2) < 0) : 6 * c ≤ 5 * d ∧ (a * d - b * c < 2 * c - d → 4 * c ≤ 3 * d) := by
    let A : Fin 4 → Matrix (Fin a) (Fin b) ℂ := fun i => X (p i)
    let B : Fin 4 → Matrix (Fin d) (Fin c) ℂ := fun i => Y (p i)
    have hpres : (∑ i, kronecker (A i) (B i)) =
        ∑ i, kronecker (X i) (Y i) :=
      Equiv.sum_comp p (fun i => kronecker (X i) (Y i))
    have hF' : (∑ i, kronecker (A i) (B i))ᴴ *
        (∑ i, kronecker (A i) (B i)) = 1 := by rw [hpres, hF]
    have hX' : (∑ i, (A i)ᴴ * A i) = 1 :=
      (Equiv.sum_comp p (fun i => (X i)ᴴ * X i)).trans hX
    have hD : NativeFourKernel.compression A
        (diagonal ![(f (p 0) : ℂ), (f (p 1) : ℂ), (f (p 2) : ℂ), 0]) = 0 := by
      have heq : ![(f (p 0) : ℂ), (f (p 1) : ℂ), (f (p 2) : ℂ), 0] =
          (fun i => (f (p i) : ℂ)) := by
        funext i
        fin_cases i <;> simp [h3]
      rw [heq, NativeFourKernel.compression, NativeRectangularBound.stackK_compression]
      simp only [Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      exact (Equiv.sum_comp p (fun i => (f i : ℂ) • ((X i)ᴴ * X i))).trans hf
    exact bounds_of_ordered_diagonal_compression A B hab hF' hX'
      (f (p 0)) (-f (p 1)) (-f (p 2)) (neg_pos.mpr h1) (neg_pos.mpr h2)
      (by simpa only [Complex.ofReal_neg, neg_neg] using hD)
  have pairs (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
      (x < 0 ∧ y < 0) ∨ (0 < x ∧ 0 < y) ∨
      (x < 0 ∧ z < 0) ∨ (0 < x ∧ 0 < z) ∨
      (y < 0 ∧ z < 0) ∨ (0 < y ∧ 0 < z) := by
    rcases lt_or_gt_of_ne hx with hx | hx <;>
      rcases lt_or_gt_of_ne hy with hy | hy <;>
      rcases lt_or_gt_of_ne hz with hz | hz <;> aesop
  rcases pairs (e (p0 0)) (e (p0 1)) (e (p0 2))
      (hfirst 0 (by decide)) (hfirst 1 (by decide)) (hfirst 2 (by decide)) with
    h | h | h | h | h | h
  · exact ordered e hsum ((Equiv.swap 0 2).trans p0)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using hlast)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h.2)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h.1)
  · exact ordered (fun i => -e i) hneg ((Equiv.swap 0 2).trans p0)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using neg_eq_zero.mpr hlast)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using neg_lt_zero.mpr h.2)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using neg_lt_zero.mpr h.1)
  · exact ordered e hsum ((Equiv.swap 0 1).trans p0)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using hlast)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h.1)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h.2)
  · exact ordered (fun i => -e i) hneg ((Equiv.swap 0 1).trans p0)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using neg_eq_zero.mpr hlast)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using neg_lt_zero.mpr h.1)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using neg_lt_zero.mpr h.2)
  · exact ordered e hsum p0 hlast h.1 h.2
  · exact ordered (fun i => -e i) hneg p0 (neg_eq_zero.mpr hlast)
      (neg_lt_zero.mpr h.1) (neg_lt_zero.mpr h.2)

/-- A rank-three Hermitian coefficient form forces the six-fifths bound.
If the row defect is smaller than the guaranteed right kernel dimension,
the stronger four-thirds bound follows. -/
theorem rank_three_small_defect_four_bound {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (lam : ℝ) (hlam : 0 < lam) (hab : a < b)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) =
      (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ))
    (hK : ∃ T : Matrix (Fin 4) (Fin 4) ℂ, T.IsHermitian ∧
      NativeFourKernel.compression X T = 0 ∧ T.rank = 3) :
    6 * c ≤ 5 * d ∧ (a * d - b * c < 2 * c - d → 4 * c ≤ 3 * d) := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  by_cases hY : LinearIndependent ℂ Y
  · obtain ⟨T, hT, hcomp, hrank⟩ := hK
    let V : Fin 4 → Matrix (Fin d) (Fin c) ℂ := fun i => ((Real.sqrt lam)⁻¹ : ℂ) • Y i
    have hunit : (∑ i, kronecker (X i) (V i))ᴴ * (∑ i, kronecker (X i) (V i)) = 1 := by
      have hroot : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
      have hcoef : ((Real.sqrt lam)⁻¹ : ℂ) *
          (((Real.sqrt lam)⁻¹ : ℂ) * (lam : ℂ)) = 1 := by
        exact_mod_cast (show (Real.sqrt lam)⁻¹ * ((Real.sqrt lam)⁻¹ * lam) = 1 by
          field_simp [hroot]
          nlinarith [Real.sq_sqrt hlam.le])
      have hscale : (∑ i, kronecker (X i) (V i)) =
          ((Real.sqrt lam)⁻¹ : ℂ) • (∑ i, kronecker (X i) (Y i)) := by
        simp only [V, Matrix.kronecker, Matrix.kronecker_smul, ← Finset.smul_sum]
      rw [hscale, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        hF, smul_smul, smul_smul]
      simp [mul_assoc, hcoef]
    have hV : LinearIndependent ℂ V :=
      hY.units_smul (fun _ => Units.mk0 _ (by positivity : ((Real.sqrt lam)⁻¹ : ℂ) ≠ 0))
    obtain ⟨A, B, t, hA, hB, hD, hDr⟩ :=
      normalize_rank_three X V (Nat.pos_of_ne_zero hc) hV hunit T hT hcomp hrank
    exact bounds_of_diagonal_compression A B hab hA hB t hD hDr
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hY
    obtain ⟨A, B, h⟩ := reduce_right (n := 3) X Y g i hi hg
    have h3 := NativeThreeRectangularBound.native_three_rectangular_bound A B lam hlam hab
      (by simpa only [h] using hF)
    exact ⟨by omega, fun _ => by omega⟩

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree
