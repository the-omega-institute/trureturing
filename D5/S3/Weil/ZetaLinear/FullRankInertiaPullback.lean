/- GID: D5/S3/Weil/ZetaLinear/FullRankInertiaPullback
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaLinear/FullRankInertiaPullback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove that Hermitian pullback cannot increase negative index and that an explicit right inverse preserves both positive and negative inertia exactly. -/

import D5.S3.Weil.ZetaLinear.Inertia
import Mathlib.Tactic

/-!
# Full-rank inertia pullback

`Inertia.lean` proves that the positive index of a Hermitian form cannot
increase under pullback. This module supplies the negative-index companion and
then proves exact preservation of both indices when the pulling matrix admits
an explicit right inverse.

The right inverse is the certificate needed by rectangular full-rank feature
matrices. No determinant criterion or unproved Cauchy full-rank theorem is
assumed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset Submodule
open scoped ComplexOrder

namespace RHLinalg

variable {K : Type*} [RCLike K]
variable {m d : Type*}
variable [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]

private lemma rank_hermNegPart_eq_negIndex
    {A : Matrix m m K} (hA : A.IsHermitian) :
    (hermNegPart hA).rank = negIndex hA := by
  unfold hermNegPart negIndex
  rw [rank_specMap]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq,
    negPart_eq_zero, not_le]

open Unitary in
private theorem posDefOn_neg_range_hermNegPart
    {A : Matrix m m K} (hA : A.IsHermitian) :
    PosDefOn (-A) (LinearMap.range (hermNegPart hA).mulVecLin) := by
  rintro _ ⟨y, rfl⟩ hne
  set U : Matrix m m K := ↑hA.eigenvectorUnitary
  set z := (hermNegPart hA).mulVecLin y with hz_def
  change z ≠ 0 at hne
  change 0 < hermForm (-A) z
  set d := star U *ᵥ y with hd_def
  have hc_eq : star U *ᵥ z =
      fun i => (((hA.eigenvalues i)⁻ : ℝ) : K) * d i := by
    have hz' : z = hermNegPart hA *ᵥ y := rfl
    rw [hz']
    unfold hermNegPart specMap
    rw [conjStarAlgAut_apply, Matrix.mulVec_mulVec, ← mul_assoc,
      ← mul_assoc,
      Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul,
      ← Matrix.mulVec_mulVec, ← hd_def]
    funext i
    simp only [mulVec, diagonal_dotProduct]
  have hformA : hermForm A z =
      ∑ i, hA.eigenvalues i * ((hA.eigenvalues i)⁻) ^ 2 * ‖d i‖ ^ 2 := by
    have hAz : A *ᵥ z = specMap hA id *ᵥ z := by
      rw [specMap_id]
    unfold hermForm
    rw [hAz, hermForm_specMap hA id z, hc_eq]
    refine sum_congr rfl fun i _ => ?_
    simp only [id_eq, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    ring
  have hformNegA : hermForm (-A) z =
      ∑ i, (-hA.eigenvalues i) * ((hA.eigenvalues i)⁻) ^ 2 * ‖d i‖ ^ 2 := by
    have hnegform : hermForm (-A) z = -hermForm A z := by
      unfold hermForm
      rw [neg_mulVec, dotProduct_neg, map_neg]
    rw [hnegform, hformA, ← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hformNegA]
  have hterm_nonneg : ∀ i,
      0 ≤ (-hA.eigenvalues i) * ((hA.eigenvalues i)⁻) ^ 2 * ‖d i‖ ^ 2 := by
    intro i
    rcases le_or_gt 0 (hA.eigenvalues i) with h | h
    · simp [negPart_eq_zero.mpr h]
    · exact mul_nonneg
        (mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg _))
        (sq_nonneg _)
  refine sum_pos' (fun i _ => hterm_nonneg i) ?_
  have hUinj : Function.Injective (star U *ᵥ ·) := by
    intro a b hab
    have hab' : star U *ᵥ a = star U *ᵥ b := hab
    have : (U * star U) *ᵥ a = (U * star U) *ᵥ b := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab']
    rwa [Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2,
      one_mulVec, one_mulVec] at this
  have hc_ne :
      (fun i => (((hA.eigenvalues i)⁻ : ℝ) : K) * d i) ≠ 0 := by
    rw [← hc_eq]
    intro h
    exact hne (hUinj (h.trans (mulVec_zero _).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc_ne
  refine ⟨i, mem_univ i, ?_⟩
  simp only [Pi.zero_apply, mul_ne_zero_iff, RCLike.ofReal_ne_zero] at hi
  have hevi : hA.eigenvalues i < 0 := by
    by_contra h
    exact hi.1 (negPart_eq_zero.mpr (not_lt.mp h))
  have hdi : (0 : ℝ) < ‖d i‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hi.2) 2
  have hnp : (0 : ℝ) < ((hA.eigenvalues i)⁻) ^ 2 := by
    rw [negPart_eq_neg.mpr hevi.le]
    exact pow_pos (neg_pos.mpr hevi) 2
  exact mul_pos (mul_pos (neg_pos.mpr hevi) hnp) hdi

private theorem finrank_le_negIndex_of_posDefOn_neg
    {A : Matrix m m K} (hA : A.IsHermitian)
    {W : Submodule K (m → K)} (hW : PosDefOn (-A) W) :
    Module.finrank K W ≤ negIndex hA := by
  set L : (m → K) →ₗ[K] (m → K) := (hermNegPart hA).mulVecLin
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : hermNegPart hA *ᵥ x = 0 := hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hnegDecomp : -A = hermNegPart hA - hermPosPart hA := by
      have h := hermPosPart_sub_hermNegPart hA
      have h2 : -A = -(hermPosPart hA - hermNegPart hA) := by rw [h]
      rw [neg_sub] at h2
      exact h2
    have hform_le : hermForm (-A) x ≤ 0 := by
      rw [hnegDecomp, hermForm_sub]
      have hnegZero : hermForm (hermNegPart hA) x = 0 := by
        unfold hermForm
        rw [hxL']
        simp
      rw [hnegZero, zero_sub]
      exact neg_nonpos.mpr
        (hermForm_nonneg_of_posSemidef (hermPosPart_posSemidef hA) x)
    exact absurd (hW x hxW hne') (not_lt.mpr hform_le)
  calc
    Module.finrank K W
        = Module.finrank K (LinearMap.range (L.domRestrict W)) :=
          (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank K (LinearMap.range L) := by
      apply Submodule.finrank_mono
      rintro y ⟨⟨x, hxW⟩, rfl⟩
      exact ⟨x, rfl⟩
    _ = (hermNegPart hA).rank := rfl
    _ = negIndex hA := rank_hermNegPart_eq_negIndex hA

/-- Pulling back a Hermitian form cannot increase its negative index. -/
theorem negIndex_conj_le
    {Q : Matrix m m K} (hQ : Q.IsHermitian) (B : Matrix m d K) :
    negIndex (isHermitian_conjTranspose_mul_mul B hQ) ≤ negIndex hQ := by
  set M : Matrix d d K := Bᴴ * Q * B
  set hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul B hQ
  set Vn := LinearMap.range (hermNegPart hM).mulVecLin
  have hdimV : Module.finrank K Vn = negIndex hM := by
    change (hermNegPart hM).rank = negIndex hM
    exact rank_hermNegPart_eq_negIndex hM
  have hnegV : PosDefOn (-M) Vn :=
    posDefOn_neg_range_hermNegPart hM
  let LB : (d → K) →ₗ[K] (m → K) := B.mulVecLin
  have hnegPull : Bᴴ * (-Q) * B = -M := by
    simp [M]
  have hinj : Function.Injective (LB.domRestrict Vn) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxV⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : B *ᵥ x = 0 := hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos : 0 < hermForm (-M) x := hnegV x hxV hne'
    rw [← hnegPull, hermForm_conj (-Q) B x, hxL'] at hpos
    simp [hermForm] at hpos
  have hnegBV : PosDefOn (-Q) (LinearMap.range (LB.domRestrict Vn)) := by
    rintro _ ⟨⟨x, hxV⟩, rfl⟩ hne
    simp only [LinearMap.domRestrict_apply, LB, mulVecLin_apply] at *
    have hne' : x ≠ 0 := by
      rintro rfl
      apply hne
      simp
    rw [← hermForm_conj (-Q) B x, hnegPull]
    exact hnegV x hxV hne'
  calc
    negIndex hM = Module.finrank K Vn := hdimV.symm
    _ = Module.finrank K (LinearMap.range (LB.domRestrict Vn)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ negIndex hQ := finrank_le_negIndex_of_posDefOn_neg hQ hnegBV

/-- If the pulling matrix has an explicit right inverse, positive index is
preserved exactly. -/
theorem posIndex_conj_eq_of_rightInverse
    {Q : Matrix m m K} (hQ : Q.IsHermitian)
    (B : Matrix m d K) (R : Matrix d m K)
    (hBR : B * R = 1) :
    posIndex (isHermitian_conjTranspose_mul_mul B hQ) = posIndex hQ := by
  let hPull : (Bᴴ * Q * B).IsHermitian :=
    isHermitian_conjTranspose_mul_mul B hQ
  have hforward : posIndex hPull ≤ posIndex hQ := posIndex_conj_le hQ B
  have hrecover : Rᴴ * (Bᴴ * Q * B) * R = Q := by
    calc
      Rᴴ * (Bᴴ * Q * B) * R = (B * R)ᴴ * Q * (B * R) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Q := by
        rw [hBR]
        simp
  have hbackRaw :
      posIndex (isHermitian_conjTranspose_mul_mul R hPull) ≤ posIndex hPull :=
    posIndex_conj_le hPull R
  have hback : posIndex hQ ≤ posIndex hPull := by
    have htrans :
        posIndex (isHermitian_conjTranspose_mul_mul R hPull) = posIndex hQ := by
      congr 1
    calc posIndex hQ
        = posIndex (isHermitian_conjTranspose_mul_mul R hPull) := htrans.symm
      _ ≤ posIndex hPull := hbackRaw
  exact le_antisymm hforward hback

/-- If the pulling matrix has an explicit right inverse, negative index is
preserved exactly. -/
theorem negIndex_conj_eq_of_rightInverse
    {Q : Matrix m m K} (hQ : Q.IsHermitian)
    (B : Matrix m d K) (R : Matrix d m K)
    (hBR : B * R = 1) :
    negIndex (isHermitian_conjTranspose_mul_mul B hQ) = negIndex hQ := by
  let hPull : (Bᴴ * Q * B).IsHermitian :=
    isHermitian_conjTranspose_mul_mul B hQ
  have hforward : negIndex hPull ≤ negIndex hQ := negIndex_conj_le hQ B
  have hrecover : Rᴴ * (Bᴴ * Q * B) * R = Q := by
    calc
      Rᴴ * (Bᴴ * Q * B) * R = (B * R)ᴴ * Q * (B * R) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Q := by
        rw [hBR]
        simp
  have hbackRaw :
      negIndex (isHermitian_conjTranspose_mul_mul R hPull) ≤ negIndex hPull :=
    negIndex_conj_le hPull R
  have hback : negIndex hQ ≤ negIndex hPull := by
    have htrans :
        negIndex (isHermitian_conjTranspose_mul_mul R hPull) = negIndex hQ := by
      congr 1
    calc negIndex hQ
        = negIndex (isHermitian_conjTranspose_mul_mul R hPull) := htrans.symm
      _ ≤ negIndex hPull := hbackRaw
  exact le_antisymm hforward hback

/-- An explicit right inverse preserves the full positive/negative inertia
pair of a Hermitian form under pullback. -/
theorem inertia_conj_eq_of_rightInverse
    {Q : Matrix m m K} (hQ : Q.IsHermitian)
    (B : Matrix m d K) (R : Matrix d m K)
    (hBR : B * R = 1) :
    posIndex (isHermitian_conjTranspose_mul_mul B hQ) = posIndex hQ ∧
      negIndex (isHermitian_conjTranspose_mul_mul B hQ) = negIndex hQ := by
  exact ⟨
    posIndex_conj_eq_of_rightInverse hQ B R hBR,
    negIndex_conj_eq_of_rightInverse hQ B R hBR⟩

#print axioms negIndex_conj_le
#print axioms posIndex_conj_eq_of_rightInverse
#print axioms negIndex_conj_eq_of_rightInverse
#print axioms inertia_conj_eq_of_rightInverse

end RHLinalg
