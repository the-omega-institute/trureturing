/- GID: D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum
   mirror-E: none(waiver:analytic-universal-theorem)
   anchors: []
   utility: none
   digest: Exact coherence minimization for rank-two three-column real or complex frames. -/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.QuantumBounds.Designs.CrossFrameRankTwoMinimum
open Matrix
open scoped BigOperators ComplexOrder
variable {K : Type*} [RCLike K]

/-- Both families have two rows and three columns. -/
def Dual (F G : Matrix (Fin 2) (Fin 3) K) : Prop := F * Gᴴ = 1

/-- The ordered cross-Gram matrix, with the first column family conjugated. -/
def crossGram (F G : Matrix (Fin 2) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K := Fᴴ * G

/-- Maximum over all six ordered off-diagonal entries. -/
def coherence (C : Matrix (Fin 3) (Fin 3) K) : ℝ :=
  (((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 ≠ p.2)).sup
    (fun p => ‖C p.1 p.2‖₊) : NNReal)

/-- Support of the null vector. -/
def support (u : Fin 3 → K) : Finset (Fin 3) := Finset.univ.filter (fun i => u i ≠ 0)

/-- Largest magnitude away from a coordinate. -/
def weight (u : Fin 3 → K) (i : Fin 3) : ℝ :=
  (((Finset.univ : Finset (Fin 3)).erase i).sup (fun j => ‖u j‖₊) : NNReal)

/-- The reciprocal-minimum denominator. -/
def total (u : Fin 3 → K) : ℝ := ∑ i, ‖u i‖ / weight u i

/-- The normalized codimension-one cross-Gram matrix. -/
def gram (u v : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K := 1 - vecMulVec v (star u)

/-- Explicit reconstruction from a proposed cross-Gram matrix. -/
def reconstruct (F : Matrix (Fin 2) (Fin 3) K) (C : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 2) (Fin 3) K := (F * Fᴴ)⁻¹ * F * C

private lemma dual_adjoint {F G : Matrix (Fin 2) (Fin 3) K} (h : Dual F G) :
    G * Fᴴ = 1 := by
  simpa only [Dual, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one]
    using congrArg Matrix.conjTranspose h

private lemma row_surjective (F : Matrix (Fin 2) (Fin 3) K) (hr : F.rank = 2) :
    Function.Surjective F.mulVec := by
  have hr' : Module.finrank K (LinearMap.range F.mulVecLin) = 2 := hr
  have htop : LinearMap.range F.mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq <| by
    simpa only [Module.finrank_pi, Fintype.card_fin] using hr'
  exact LinearMap.range_eq_top.mp htop

private lemma columns_span (F : Matrix (Fin 2) (Fin 3) K)
    (h : Function.Surjective F.mulVec) : Submodule.span K (Set.range F.col) = ⊤ := by
  rw [← Matrix.range_mulVecLin]
  exact LinearMap.range_eq_top.mpr h

private lemma dual_columns_span (F G : Matrix (Fin 2) (Fin 3) K) (h : Dual F G) :
    Submodule.span K (Set.range G.col) = ⊤ := by
  apply columns_span
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  exact ⟨Fᴴ, dual_adjoint h⟩

private lemma kernel_span (F : Matrix (Fin 2) (Fin 3) K) (hr : F.rank = 2)
    (u : Fin 3 → K) (hu : u ≠ 0) (hFu : F *ᵥ u = 0) :
    LinearMap.ker F.mulVecLin = Submodule.span K {u} := by
  have hdim := LinearMap.finrank_range_add_finrank_ker F.mulVecLin
  have hk : Module.finrank K (LinearMap.ker F.mulVecLin) = 1 := by
    change F.rank + _ = _ at hdim
    simp only [Module.finrank_pi, Fintype.card_fin, hr] at hdim
    omega
  exact eq_span_singleton_of_mem_of_finrank_eq_one hk hFu hu

private lemma gram_unit (F : Matrix (Fin 2) (Fin 3) K) (hr : F.rank = 2) :
    IsUnit (F * Fᴴ).det := by
  have ht : LinearMap.range (F * Fᴴ).mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq <| by
      change (F * Fᴴ).rank = _
      simpa only [rank_self_mul_conjTranspose, Module.finrank_pi, Fintype.card_fin] using hr
  exact (Matrix.isUnit_iff_isUnit_det (F * Fᴴ)).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp (LinearMap.range_eq_top.mp ht))

private lemma null_outer (F : Matrix (Fin 2) (Fin 3) K) (u : Fin 3 → K)
    (hk : LinearMap.ker F.mulVecLin = Submodule.span K {u})
    (D : Matrix (Fin 3) (Fin 3) K) (hD : F * D = 0) :
    ∃ w : Fin 3 → K, D = vecMulVec u w := by
  have hc (j : Fin 3) : D.col j ∈ Submodule.span K {u} := by
    rw [← hk]
    change F *ᵥ D.col j = 0
    ext i
    exact congrFun₂ hD i j
  choose w hw using fun j => Submodule.mem_span_singleton.mp (hc j)
  refine ⟨w, ?_⟩
  ext i j
  exact (congrFun (hw j) i).symm.trans (mul_comm _ _)

private lemma parameter_of_dual (F G : Matrix (Fin 2) (Fin 3) K)
    (u : Fin 3 → K) (hu : u ≠ 0) (hFu : F *ᵥ u = 0)
    (hk : LinearMap.ker F.mulVecLin = Submodule.span K {u}) (hd : Dual F G) :
    ∃ v : Fin 3 → K, (star u) ⬝ᵥ v = 1 ∧ crossGram F G = gram u v := by
  have hz : F * (1 - Gᴴ * F) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hd]
    simp
  obtain ⟨w, hw⟩ := null_outer F u hk (1 - Gᴴ * F) hz
  have hc : crossGram F G = gram u (star w) := by
    have hh := congrArg Matrix.conjTranspose hw
    have hh' : 1 - crossGram F G = vecMulVec (star w) (star u) := by
      simpa [crossGram, conjTranspose_sub, conjTranspose_mul,
        Matrix.conjTranspose_vecMulVec] using hh
    calc
      crossGram F G = 1 - (1 - crossGram F G) := by abel
      _ = gram u (star w) := by rw [hh']; rfl
  have hz' : (star u) ᵥ* crossGram F G = 0 := by
    have ht : (star u) ᵥ* Fᴴ = 0 := by
      simpa only [star_mulVec, star_zero] using congrArg star hFu
    rw [crossGram, ← vecMul_vecMul, ht, zero_vecMul]
  have heq : (star u) ⬝ᵥ star w = 1 := by
    rw [hc, gram, vecMul_sub, vecMul_one, vecMul_vecMulVec] at hz'
    obtain ⟨r, hr⟩ : ∃ r, u r ≠ 0 := Function.ne_iff.mp hu
    have h := congrFun hz' r
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have hru : star (u r) ≠ 0 := star_ne_zero.mpr hr
    apply (mul_right_cancel₀ hru)
    linear_combination -h
  exact ⟨star w, heq, hc⟩

private lemma reconstructed (F : Matrix (Fin 2) (Fin 3) K) (hr : F.rank = 2)
    (u v : Fin 3 → K) (hu : u ≠ 0) (hFu : F *ᵥ u = 0)
    (hv : (star u) ⬝ᵥ v = 1) :
    Dual F (reconstruct F (gram u v)) ∧
      crossGram F (reconstruct F (gram u v)) = gram u v := by
  have hi := gram_unit F hr
  let B : Matrix (Fin 2) (Fin 3) K := (F * Fᴴ)⁻¹ * F
  have hB : B * Fᴴ = 1 := by
    dsimp [B]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul (F * Fᴴ) hi]
  have hBd : Dual F B := by
    have := congrArg Matrix.conjTranspose hB
    simpa only [Dual, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] using this
  obtain ⟨z, _, hz⟩ := parameter_of_dual F B u hu hFu (kernel_span F hr u hu hFu) hBd
  have hleft : crossGram F B * gram u v = gram u v := by
    rw [hz, gram, gram]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, vecMulVec_mul_vecMulVec, hv, one_smul]
    abel
  have hcross : crossGram F (reconstruct F (gram u v)) = gram u v := by
    change Fᴴ * (B * gram u v) = _
    rw [← Matrix.mul_assoc]
    exact hleft
  have hrow : (star u) ᵥ* Fᴴ = 0 := by
    simpa only [star_mulVec, star_zero] using congrArg star hFu
  have hcF : gram u v * Fᴴ = Fᴴ := by
    rw [gram, Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul, hrow]
    ext i j
    simp [vecMulVec_apply]
  have hd : Dual F (reconstruct F (gram u v)) := by
    have he : reconstruct F (gram u v) * Fᴴ = 1 := by
      change B * gram u v * Fᴴ = 1
      rw [Matrix.mul_assoc, hcF, hB]
    have := congrArg Matrix.conjTranspose he
    simpa only [Dual, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] using this
  exact ⟨hd, hcross⟩

private lemma coherence_nonneg (C : Matrix (Fin 3) (Fin 3) K) : 0 ≤ coherence C :=
  NNReal.coe_nonneg _

private lemma entry_le (C : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) (hij : i ≠ j) :
    ‖C i j‖ ≤ coherence C := by
  exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun p : Fin 3 × Fin 3 => ‖C p.1 p.2‖₊)
    (by simp [hij] : (i,j) ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 ≠ p.2)))

private lemma coherence_le (C : Matrix (Fin 3) (Fin 3) K) (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ i j, i ≠ j → ‖C i j‖ ≤ t) : coherence C ≤ t := by
  change ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 ≠ p.2)).sup
    (fun p => ‖C p.1 p.2‖₊) ≤ (⟨t, ht⟩ : NNReal)
  apply Finset.sup_le
  intro p hp
  change ‖C p.1 p.2‖ ≤ t
  exact h p.1 p.2 (Finset.mem_filter.mp hp).2

private lemma norm_le_weight (u : Fin 3 → K) (i j : Fin 3) (hji : j ≠ i) :
    ‖u j‖ ≤ weight u i := by
  exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j => ‖u j‖₊) (by simp [hji]))

private lemma weight_nonneg (u : Fin 3 → K) (i : Fin 3) : 0 ≤ weight u i :=
  NNReal.coe_nonneg _

private lemma weight_le (u : Fin 3 → K) (i : Fin 3) (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ j, j ≠ i → ‖u j‖ ≤ t) : weight u i ≤ t := by
  change ((Finset.univ : Finset (Fin 3)).erase i).sup (fun j => ‖u j‖₊) ≤ (⟨t, ht⟩ : NNReal)
  apply Finset.sup_le
  intro j hj
  change ‖u j‖ ≤ t
  exact h j (Finset.mem_erase.mp hj).1

private lemma gram_offdiag (u v : Fin 3 → K) (i j : Fin 3) (hij : i ≠ j) :
    ‖gram u v i j‖ = ‖v i‖ * ‖u j‖ := by
  simp [gram, vecMulVec_apply, hij, norm_mul]

private lemma row_bound (u v : Fin 3 → K) (i : Fin 3) :
    weight u i * ‖v i‖ ≤ coherence (gram u v) := by
  by_cases hz : v i = 0
  · simpa [hz] using coherence_nonneg (gram u v)
  have hp : 0 < ‖v i‖ := norm_pos_iff.mpr hz
  apply (le_div_iff₀ hp).mp
  apply weight_le u i _ (div_nonneg (coherence_nonneg _) (norm_nonneg _))
  intro j hji
  apply (le_div_iff₀ hp).mpr
  simpa only [gram_offdiag u v i j hji.symm, mul_comm] using entry_le (gram u v) i j hji.symm

private lemma gram_le (u v : Fin 3 → K) (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ i, weight u i * ‖v i‖ ≤ t) : coherence (gram u v) ≤ t := by
  apply coherence_le _ t ht
  intro i j hij
  rw [gram_offdiag u v i j hij, mul_comm]
  exact (mul_le_mul_of_nonneg_right (norm_le_weight u i j hij.symm) (norm_nonneg _)).trans (h i)

private lemma coherence_eq_max (u v : Fin 3 → K) :
    coherence (gram u v) = Finset.univ.sup' Finset.univ_nonempty
      (fun i => weight u i * ‖v i‖) := by
  apply le_antisymm
  · apply gram_le
    · exact (mul_nonneg (weight_nonneg u 0) (norm_nonneg (v 0))).trans
        (Finset.le_sup' (fun i => weight u i * ‖v i‖) (Finset.mem_univ 0))
    · intro i
      exact Finset.le_sup' (fun i : Fin 3 => weight u i * ‖v i‖) (Finset.mem_univ i)
  · exact Finset.sup'_le _ _ (fun i _ => row_bound u v i)

private lemma weight_pos (u : Fin 3 → K) (hs : 2 ≤ (support u).card) (i : Fin 3) :
    0 < weight u i := by
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (by omega : 1 < (support u).card)
  have hj0 : u j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hk0 : u k ≠ 0 := (Finset.mem_filter.mp hk).2
  by_cases hji : j = i
  · exact (norm_pos_iff.mpr hk0).trans_le (norm_le_weight u i k (by aesop))
  · exact (norm_pos_iff.mpr hj0).trans_le (norm_le_weight u i j hji)

private lemma total_pos (u : Fin 3 → K) (hu : u ≠ 0) (hs : 2 ≤ (support u).card) :
    0 < total u := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  apply Finset.sum_pos'
  · intro j _
    exact div_nonneg (norm_nonneg _) (weight_nonneg u j)
  · exact ⟨i, Finset.mem_univ i, div_pos (norm_pos_iff.mpr hi) (weight_pos u hs i)⟩

private lemma lower_bound (u v : Fin 3 → K) (hu : u ≠ 0)
    (hs : 2 ≤ (support u).card) (hv : (star u) ⬝ᵥ v = 1) :
    (total u)⁻¹ ≤ coherence (gram u v) := by
  have htriangle : 1 ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    have h := norm_sum_le (Finset.univ : Finset (Fin 3)) (fun i => star (u i) * v i)
    change ∑ i, star (u i) * v i = 1 at hv
    simpa only [hv, norm_one, norm_mul, norm_star] using h
  have hsum : (∑ i, ‖u i‖ * ‖v i‖) ≤ coherence (gram u v) * total u := by
    rw [total, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb : weight u i * ‖v i‖ ≤ coherence (gram u v) := by
      rw [coherence_eq_max]
      exact Finset.le_sup' (fun i : Fin 3 => weight u i * ‖v i‖) (Finset.mem_univ i)
    have h := (le_div_iff₀ (weight_pos u hs i)).mpr
      (by simpa only [mul_comm] using hb)
    calc
      ‖u i‖ * ‖v i‖ ≤ ‖u i‖ * (coherence (gram u v) / weight u i) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = coherence (gram u v) * (‖u i‖ / weight u i) := by ring
  rw [← one_div]
  exact (div_le_iff₀ (total_pos u hu hs)).mpr (htriangle.trans hsum)

/-- The zero-coordinate convention is explicit. -/
def optimalParameter (u : Fin 3 → K) (i : Fin 3) : K :=
  if u i = 0 then 0 else (((total u)⁻¹ / weight u i : ℝ) : K) *
    (u i / ((‖u i‖ : ℝ) : K))

private lemma optimizer_norm (u : Fin 3 → K) (hu : u ≠ 0)
    (hs : 2 ≤ (support u).card) (i : Fin 3) :
    ‖optimalParameter u i‖ = if u i = 0 then 0 else (total u)⁻¹ / weight u i := by
  by_cases hi : u i = 0
  · simp [optimalParameter, hi]
  have hn : ‖u i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
  have ht : 0 ≤ (total u)⁻¹ / weight u i :=
    div_nonneg (inv_nonneg.mpr (total_pos u hu hs).le) (weight_nonneg u i)
  simp only [optimalParameter, if_neg hi, norm_mul, norm_div, RCLike.norm_ofReal,
    abs_of_nonneg ht, abs_of_nonneg (norm_nonneg (u i)), div_self hn, mul_one]

private lemma optimizer_product (u : Fin 3 → K) (i : Fin 3) :
    star (u i) * optimalParameter u i =
      (((total u)⁻¹ * (‖u i‖ / weight u i) : ℝ) : K) := by
  by_cases hi : u i = 0
  · simp [optimalParameter, hi]
  have hn : ((‖u i‖ : ℝ) : K) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hi
  have hh := RCLike.conj_mul (u i)
  change star (u i) * u i = ((‖u i‖ : ℝ) : K) ^ 2 at hh
  let r : K := (((total u)⁻¹ / weight u i : ℝ) : K)
  calc
    star (u i) * optimalParameter u i = r * (star (u i) * u i) / ((‖u i‖ : ℝ) : K) := by
      simp only [optimalParameter, if_neg hi]
      dsimp only [r]
      ring
    _ = r * ((‖u i‖ : ℝ) : K) := by rw [hh]; field_simp
    _ = (((total u)⁻¹ * (‖u i‖ / weight u i) : ℝ) : K) := by
      dsimp only [r]
      push_cast
      ring

private lemma optimizer_normalized (u : Fin 3 → K) (hu : u ≠ 0)
    (hs : 2 ≤ (support u).card) : (star u) ⬝ᵥ optimalParameter u = 1 := by
  change (∑ i, star (u i) * optimalParameter u i) = 1
  simp_rw [optimizer_product]
  rw [← RCLike.ofReal_sum, ← Finset.mul_sum]
  change (((total u)⁻¹ * total u : ℝ) : K) = 1
  rw [inv_mul_cancel₀ (ne_of_gt (total_pos u hu hs)), RCLike.ofReal_one]

private lemma optimizer_attains (u : Fin 3 → K) (hu : u ≠ 0)
    (hs : 2 ≤ (support u).card) :
    coherence (gram u (optimalParameter u)) = (total u)⁻¹ := by
  apply le_antisymm
  · apply gram_le _ _ _ (inv_nonneg.mpr (total_pos u hu hs).le)
    intro i
    rw [optimizer_norm u hu hs i]
    split_ifs with hi
    · simpa using (inv_nonneg.mpr (total_pos u hu hs).le)
    · rw [mul_div_cancel₀ _ (ne_of_gt (weight_pos u hs i))]
  · exact lower_bound u (optimalParameter u) hu hs (optimizer_normalized u hu hs)

private lemma cross_injective (F : Matrix (Fin 2) (Fin 3) K) (hr : F.rank = 2) :
    Function.Injective (crossGram F) := by
  intro G H hGH
  have hB : ((F * Fᴴ)⁻¹ * F) * Fᴴ = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul (F * Fᴴ) (gram_unit F hr)]
  have hh := congrArg (fun C => ((F * Fᴴ)⁻¹ * F) * C) hGH
  simpa only [crossGram, ← Matrix.mul_assoc, hB, Matrix.one_mul] using hh

/-- Actual duals are the normalized rank-one corrections, with explicit reconstruction. -/
theorem dual_parameterization (F : Matrix (Fin 2) (Fin 3) K) (hr : F.rank = 2)
    (u : Fin 3 → K) (hu : u ≠ 0) (hFu : F *ᵥ u = 0)
    (G : Matrix (Fin 2) (Fin 3) K) :
    Dual F G ↔ ∃ v : Fin 3 → K, (star u) ⬝ᵥ v = 1 ∧
      crossGram F G = gram u v ∧ G = reconstruct F (gram u v) := by
  constructor
  · intro hd
    obtain ⟨v, hv, hc⟩ := parameter_of_dual F G u hu hFu (kernel_span F hr u hu hFu) hd
    refine ⟨v, hv, hc, cross_injective F hr ?_⟩
    exact hc.trans (reconstructed F hr u v hu hFu hv).2.symm
  · rintro ⟨v, hv, _, rfl⟩
    exact (reconstructed F hr u v hu hFu hv).1

private lemma full_support_card (u : Fin 3 → K) (hu : ∀ i, u i ≠ 0) :
    2 ≤ (support u).card := by
  have hs : support u = Finset.univ := by ext i; simp [support, hu]
  simp [hs]

private lemma parameter_unique (u v : Fin 3 → K) (hu : ∀ i, u i ≠ 0)
    (hv : (star u) ⬝ᵥ v = 1)
    (hm : coherence (gram u v) ≤ (total u)⁻¹) : v = optimalParameter u := by
  have hune : u ≠ 0 := by intro h; exact hu 0 (congrFun h 0)
  have hs := full_support_card u hu
  let T : ℝ := (total u)⁻¹
  have hcap (i : Fin 3) : ‖star (u i) * v i‖ ≤ T * (‖u i‖ / weight u i) := by
    rw [norm_mul, norm_star]
    have hb := (le_div_iff₀ (weight_pos u hs i)).mpr
      (by simpa only [mul_comm] using (row_bound u v i).trans hm)
    calc
      ‖u i‖ * ‖v i‖ ≤ ‖u i‖ * (T / weight u i) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = T * (‖u i‖ / weight u i) := by ring
  have hre : ∑ i, RCLike.re (star (u i) * v i) = 1 := by
    have hh := congrArg RCLike.re hv
    simpa [dotProduct, map_sum] using hh
  have hnon (i : Fin 3) : 0 ≤ T * (‖u i‖ / weight u i) - RCLike.re (star (u i) * v i) :=
    sub_nonneg.mpr ((RCLike.re_le_norm _).trans (hcap i))
  have hzero : ∑ i, (T * (‖u i‖ / weight u i) - RCLike.re (star (u i) * v i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hre]
    change T * total u - 1 = 0
    simp [T, ne_of_gt (total_pos u hune hs)]
  have heach := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnon i)).mp hzero
  funext i
  have he : RCLike.re (star (u i) * v i) = T * (‖u i‖ / weight u i) :=
    (sub_eq_zero.mp (heach i (Finset.mem_univ i))).symm
  have hphase : star (u i) * v i = ((T * (‖u i‖ / weight u i) : ℝ) : K) := by
    have hn : ‖star (u i) * v i‖ ≤ RCLike.re (star (u i) * v i) := by rw [he]; exact hcap i
    exact (RCLike.re_eq_self_of_le hn).symm.trans (congrArg RCLike.ofReal he)
  have ho : star (u i) * optimalParameter u i = ((T * (‖u i‖ / weight u i) : ℝ) : K) :=
    optimizer_product u i
  exact mul_left_cancel₀ (star_ne_zero.mpr (hu i)) (hphase.trans ho.symm)

private lemma singleton_parameter (u : Fin 3 → K) (hs : (support u).card = 1) :
    ∃ v : Fin 3 → K, (star u) ⬝ᵥ v = 1 ∧ coherence (gram u v) = 0 := by
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hs
  have hur : u r ≠ 0 := by
    have : r ∈ support u := by rw [hr]; simp
    exact (Finset.mem_filter.mp this).2
  have hother (i : Fin 3) (hi : i ≠ r) : u i = 0 := by
    by_contra h
    have : i ∈ support u := by simp [support, h]
    rw [hr] at this
    exact hi (Finset.mem_singleton.mp this)
  let v : Fin 3 → K := fun i => if i = r then (star (u r))⁻¹ else 0
  refine ⟨v, ?_, le_antisymm ?_ (coherence_nonneg _)⟩
  · simp only [dotProduct, v, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    exact mul_inv_cancel₀ (star_ne_zero.mpr hur)
  · apply coherence_le _ 0 le_rfl
    intro i j hij
    rw [gram_offdiag u v i j hij]
    by_cases hi : i = r
    · subst i
      rw [hother j hij.symm, norm_zero, mul_zero]
    · simp [v, hi]

/-- The minimum is attained in every nonzero support case; full support makes the actual dual unique. -/
theorem rank_two_minimum (F : Matrix (Fin 2) (Fin 3) K) (hr : F.rank = 2)
    (u : Fin 3 → K) (hu : u ≠ 0) (hFu : F *ᵥ u = 0) :
    ∃ G₀ : Matrix (Fin 2) (Fin 3) K, Dual F G₀ ∧
      Submodule.span K (Set.range F.col) = ⊤ ∧
      Submodule.span K (Set.range G₀.col) = ⊤ ∧
      ((support u).card = 1 → coherence (crossGram F G₀) = 0) ∧
      (2 ≤ (support u).card → (∀ i, 0 < weight u i) ∧ 0 < total u ∧
        G₀ = reconstruct F (gram u (optimalParameter u)) ∧
        coherence (crossGram F G₀) = (total u)⁻¹) ∧
      (∀ G, Dual F G → coherence (crossGram F G₀) ≤ coherence (crossGram F G)) ∧
      ((∀ i, u i ≠ 0) → ∀ G, Dual F G →
        coherence (crossGram F G) ≤ coherence (crossGram F G₀) → G = G₀) := by
  by_cases hs : (support u).card = 1
  · obtain ⟨v, hv, hm⟩ := singleton_parameter u hs
    obtain ⟨hd, hc⟩ := reconstructed F hr u v hu hFu hv
    refine ⟨reconstruct F (gram u v), hd, columns_span F (row_surjective F hr),
      dual_columns_span F _ hd, (fun _ => by rw [hc]; exact hm), ?_, ?_, ?_⟩
    · intro h; omega
    · intro G _; rw [hc, hm]; exact coherence_nonneg _
    · intro h; have := full_support_card u h; omega
  · have hpos : 0 < (support u).card := by
      apply Finset.card_pos.mpr
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
      simp only [Pi.zero_apply] at hi
      exact ⟨i, by simp [support, hi]⟩
    have hs2 : 2 ≤ (support u).card := by omega
    have hv := optimizer_normalized u hu hs2
    obtain ⟨hd, hc⟩ := reconstructed F hr u (optimalParameter u) hu hFu hv
    have hm : coherence (crossGram F (reconstruct F (gram u (optimalParameter u)))) = (total u)⁻¹ :=
      by rw [hc]; exact optimizer_attains u hu hs2
    refine ⟨reconstruct F (gram u (optimalParameter u)), hd, columns_span F (row_surjective F hr),
      dual_columns_span F _ hd, (fun h => (hs h).elim),
      (fun _ => ⟨weight_pos u hs2, total_pos u hu hs2, rfl, hm⟩), ?_, ?_⟩
    · intro G hG
      obtain ⟨v, hv, hcv, _⟩ := (dual_parameterization F hr u hu hFu G).mp hG
      rw [hm, hcv]
      exact lower_bound u v hu hs2 hv
    · intro hfull G hG hmin
      obtain ⟨v, hv, hcv, hrec⟩ := (dual_parameterization F hr u hu hFu G).mp hG
      rw [hm, hcv] at hmin
      rw [hrec, parameter_unique u v hfull hv hmin]

#print axioms dual_parameterization
#print axioms rank_two_minimum

end D5.S3.QuantumBounds.Designs.CrossFrameRankTwoMinimum
