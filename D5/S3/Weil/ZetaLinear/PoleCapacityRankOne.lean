/- GID: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaLinear/PoleCapacityRankOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive rank-one pole update removes at most one negative direction. -/

import D5.S3.Weil.ZetaLinear.Inertia
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank-one capacity of a positive pole update

The canonical negative spectral index is subadditive under addition of Hermitian
matrices. Applying that inequality to the updated matrix and the negative of its
explicit rank-one correction bounds the loss of negative directions by one.

The repository and pinned Mathlib were searched for the complete two-clause
statement. `RHLinalg.negIndex`, `Matrix.rank_vecMulVec_le`, and the canonical
positive-semidefinite outer-product theorem were exact supporting hits; no
existing theorem stated both conclusions.
-/

noncomputable section

open Matrix Finset Submodule
open scoped ComplexOrder

namespace D5.S3.Weil.ZetaLinear.PoleCapacityRankOne

open RHLinalg

variable {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]

private lemma rank_hermNegPart_eq_negIndex {A : Matrix n n K} (hA : A.IsHermitian) :
    (hermNegPart hA).rank = negIndex hA := by
  unfold hermNegPart negIndex
  rw [rank_specMap]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, negPart_eq_zero, not_le]

open Unitary in
private theorem negDefOn_range_hermNegPart {A : Matrix n n K} (hA : A.IsHermitian) :
    PosDefOn (-A) (LinearMap.range (hermNegPart hA).mulVecLin) := by
  rintro _ ⟨y, rfl⟩ hne
  set U : Matrix n n K := ↑hA.eigenvectorUnitary
  set z := (hermNegPart hA).mulVecLin y with hz_def
  change z ≠ 0 at hne
  change 0 < hermForm (-A) z
  set d := star U *ᵥ y with hd_def
  have hc_eq : star U *ᵥ z = fun i => (((hA.eigenvalues i)⁻ : ℝ) : K) * d i := by
    have hz' : z = hermNegPart hA *ᵥ y := rfl
    rw [hz']
    unfold hermNegPart specMap
    rw [conjStarAlgAut_apply, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc,
      Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul,
      ← Matrix.mulVec_mulVec, ← hd_def]
    funext i
    simp only [mulVec, diagonal_dotProduct]
  have hformA : hermForm A z =
      ∑ i, hA.eigenvalues i * ((hA.eigenvalues i)⁻) ^ 2 * ‖d i‖ ^ 2 := by
    have hAz : A *ᵥ z = specMap hA id *ᵥ z := by rw [specMap_id]
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
  have hterm_nn : ∀ i,
      0 ≤ (-hA.eigenvalues i) * ((hA.eigenvalues i)⁻) ^ 2 * ‖d i‖ ^ 2 := by
    intro i
    rcases le_or_gt 0 (hA.eigenvalues i) with h | h
    · simp [negPart_eq_zero.mpr h]
    · exact mul_nonneg (mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg _)) (sq_nonneg _)
  refine sum_pos' (fun i _ => hterm_nn i) ?_
  have hUinj : Function.Injective (star U *ᵥ ·) := by
    intro a b hab
    have hab' : star U *ᵥ a = star U *ᵥ b := hab
    have : (U * star U) *ᵥ a = (U * star U) *ᵥ b := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hab']
    rwa [Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec,
      one_mulVec] at this
  have hc_ne : (fun i => (((hA.eigenvalues i)⁻ : ℝ) : K) * d i) ≠ 0 := by
    rw [← hc_eq]
    intro h
    exact hne (hUinj (h.trans (mulVec_zero _).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc_ne
  refine ⟨i, mem_univ i, ?_⟩
  simp only [Pi.zero_apply, mul_ne_zero_iff, RCLike.ofReal_ne_zero] at hi
  have hevi : hA.eigenvalues i < 0 := by
    by_contra h
    exact hi.1 (negPart_eq_zero.mpr (not_lt.mp h))
  have hdi : (0 : ℝ) < ‖d i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi.2) 2
  have hnp : (0 : ℝ) < ((hA.eigenvalues i)⁻) ^ 2 := by
    rw [negPart_eq_neg.mpr hevi.le]
    exact pow_pos (neg_pos.mpr hevi) 2
  exact mul_pos (mul_pos (neg_pos.mpr hevi) hnp) hdi

private theorem negIndex_add_le {A B : Matrix n n K}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    negIndex (hA.add hB) ≤ negIndex hA + negIndex hB := by
  let hAB := hA.add hB
  let V := LinearMap.range (hermNegPart hAB).mulVecLin
  have hdimV : Module.finrank K V = negIndex hAB := by
    change (hermNegPart hAB).rank = negIndex hAB
    exact rank_hermNegPart_eq_negIndex hAB
  have hnegV : PosDefOn (-(A + B)) V := negDefOn_range_hermNegPart hAB
  let LA : (n → K) →ₗ[K] (n → K) := (hermNegPart hA).mulVecLin
  let LB : (n → K) →ₗ[K] (n → K) := (hermNegPart hB).mulVecLin
  let L : V →ₗ[K] (n → K) × (n → K) :=
    (LA.domRestrict V).prod (LB.domRestrict V)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxV⟩ hxL
    simp only [LinearMap.mem_ker] at hxL
    change (LA x, LB x) = (0, 0) at hxL
    have hxLA : LA x = 0 := congrArg Prod.fst hxL
    have hxLB : LB x = 0 := congrArg Prod.snd hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hA_nonneg : 0 ≤ hermForm A x := by
      rw [← hermPosPart_sub_hermNegPart hA, hermForm_sub]
      have hnegZero : hermForm (hermNegPart hA) x = 0 := by
        unfold hermForm
        rw [show hermNegPart hA *ᵥ x = 0 by exact hxLA]
        simp
      rw [hnegZero, sub_zero]
      exact hermForm_nonneg_of_posSemidef (hermPosPart_posSemidef hA) x
    have hB_nonneg : 0 ≤ hermForm B x := by
      rw [← hermPosPart_sub_hermNegPart hB, hermForm_sub]
      have hnegZero : hermForm (hermNegPart hB) x = 0 := by
        unfold hermForm
        rw [show hermNegPart hB *ᵥ x = 0 by exact hxLB]
        simp
      rw [hnegZero, sub_zero]
      exact hermForm_nonneg_of_posSemidef (hermPosPart_posSemidef hB) x
    have hnotneg : hermForm (-(A + B)) x ≤ 0 := by
      have hnegform : hermForm (-(A + B)) x = -hermForm (A + B) x := by
        unfold hermForm
        rw [neg_mulVec, dotProduct_neg, map_neg]
      rw [hnegform, hermForm_add]
      linarith
    exact absurd (hnegV x hxV hne') (not_lt.mpr hnotneg)
  calc
    negIndex hAB = Module.finrank K V := hdimV.symm
    _ = Module.finrank K (LinearMap.range L) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank K (LinearMap.range LA) + Module.finrank K (LinearMap.range LB) := by
      calc
        Module.finrank K (LinearMap.range L)
            ≤ Module.finrank K (Submodule.prod (LinearMap.range LA) (LinearMap.range LB)) := by
              apply Submodule.finrank_mono
              rintro _ ⟨v, rfl⟩
              exact ⟨⟨v.1, rfl⟩, ⟨v.1, rfl⟩⟩
        _ = _ := by
          let e : (LinearMap.range LA) × (LinearMap.range LB) →ₗ[K]
              Submodule.prod (LinearMap.range LA) (LinearMap.range LB) := {
            toFun xy := ⟨(xy.1.1, xy.2.1), xy.1.2, xy.2.2⟩
            map_add' x y := by ext <;> rfl
            map_smul' c x := by ext <;> rfl }
          have he : Function.Bijective e := by
            constructor
            · intro x y hxy
              apply Prod.ext
              · exact Subtype.ext (congrArg (fun z => z.1.1) hxy)
              · exact Subtype.ext (congrArg (fun z => z.1.2) hxy)
            · rintro ⟨⟨x, y⟩, hx, hy⟩
              exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
          rw [← (LinearEquiv.ofBijective e he).finrank_eq, Module.finrank_prod]
    _ = negIndex hA + negIndex hB := by
      rw [show Module.finrank K (LinearMap.range LA) = (hermNegPart hA).rank by rfl,
        show Module.finrank K (LinearMap.range LB) = (hermNegPart hB).rank by rfl,
        rank_hermNegPart_eq_negIndex, rank_hermNegPart_eq_negIndex]

private lemma negIndex_le_rank {A : Matrix n n K} (hA : A.IsHermitian) :
    negIndex hA ≤ A.rank := by
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  unfold negIndex
  apply card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact ne_of_lt hi

private lemma negIndex_eq_zero_of_posSemidef {A : Matrix n n K} (hA : A.PosSemidef) :
    negIndex hA.isHermitian = 0 := by
  unfold negIndex
  rw [card_eq_zero]
  ext i
  simp [not_lt_of_ge (hA.eigenvalues_nonneg i)]

/-- Adding the positive pole correction `2 pp*` can remove at most one negative
direction. Consequently, positivity of the updated matrix forces the original
matrix to have negative index at most one. -/
theorem pole_capacity_rank_one {F0 : Matrix n n ℂ} (hF0 : F0.IsHermitian) (p : n → ℂ) :
    (negIndex hF0 - 1 ≤
      negIndex (hF0.add
        ((Matrix.posSemidef_vecMulVec_self_star p).smul (a := (2 : ℝ))
          (by norm_num)).isHermitian)) ∧
      ((F0 + (2 : ℝ) • Matrix.vecMulVec p (star p)).PosSemidef →
        negIndex hF0 ≤ 1) := by
  let poleUpdate : Matrix n n ℂ := (2 : ℝ) • Matrix.vecMulVec p (star p)
  let F := F0 + poleUpdate
  have hPole : poleUpdate.PosSemidef := by
    exact (Matrix.posSemidef_vecMulVec_self_star p).smul (by norm_num)
  let hF : F.IsHermitian := hF0.add hPole.isHermitian
  have hnegPole : negIndex hPole.isHermitian.neg ≤ 1 := by
    refine (negIndex_le_rank hPole.isHermitian.neg).trans ?_
    calc
      (-poleUpdate).rank =
          (Matrix.vecMulVec ((-2 : ℝ) • p) (star p)).rank := by
            congr 1
            ext i j
            simp [poleUpdate, Matrix.vecMulVec]
            ring
      _ ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hF0le : negIndex hF0 ≤ negIndex hF + 1 := by
    have hsub := negIndex_add_le hF hPole.isHermitian.neg
    have hbound := hsub.trans (Nat.add_le_add_left hnegPole (negIndex hF))
    simpa [F, poleUpdate] using hbound
  constructor
  · simpa only using
      (Nat.sub_le_iff_le_add.mpr (by simpa [add_comm] using hF0le))
  · intro hFpsd
    have hzero : negIndex hF = 0 := negIndex_eq_zero_of_posSemidef hFpsd
    simpa [hzero] using hF0le

#print axioms pole_capacity_rank_one

end D5.S3.Weil.ZetaLinear.PoleCapacityRankOne
