/- GID: D5/S3/Combinatorics/Geometry/RowmotionCommutationCriterion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionCommutationCriterion
   mirror-E: none(waiver:abstract-order-characterization)
   anchors: []
   utility: none
   digest: The commutation relation of legal interval-closed toggles on arbitrary partial orders. -/

import D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
import Mathlib.Order.Cover

/-! # Commutation of legal interval-closed toggles

The comparable commuting case consists of covers from a minimal point to a
maximal point. The proof transfers legality of a flip; it does not require
either flip to be legal at every convex state.
-/

open scoped symmDiff
open D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
open D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles

namespace D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion

variable {P : Type*} [PartialOrder P]

private lemma transfer_extremal_cover {x y : P} (hxy : x ⋖ y)
    (hmin : IsMin x) (hmax : IsMax y) {S T : Set P}
    (hT : T.OrdConnected)
    (agree : ∀ z, z ≠ y → (z ∈ S ↔ z ∈ T))
    (hSx : (S ∆ {x}).OrdConnected) : (T ∆ {x}).OrdConnected := by
  classical
  have flip_agree (z : P) (hz : z ≠ y) :
      z ∈ S ∆ {x} ↔ z ∈ T ∆ {x} := by
    simp only [Set.mem_symmDiff, Set.mem_singleton_iff, agree z hz]
  constructor
  intro u hu v hv z hz
  by_cases hux : u = x
  · subst u
    by_cases hvy : v = y
    · subst v
      rcases hxy.eq_or_eq hz.1 hz.2 with hzx | hzy
      · simpa only [hzx] using hu
      · simpa only [hzy] using hv
    have hzy : z ≠ y := by
      intro hzy
      subst z
      exact hvy (le_antisymm (hmax hz.2) hz.2)
    exact (flip_agree z hzy).mp
      (hSx.out ((flip_agree x hxy.lt.ne).mpr hu)
        ((flip_agree v hvy).mpr hv) hz)
  · have hzx : z ≠ x := by
      intro hzx
      subst z
      exact hux (le_antisymm hz.1 (hmin hz.1))
    have hvx : v ≠ x := by
      intro hvx
      subst v
      have hux' : u ≤ x := le_trans hz.1 hz.2
      exact hux (le_antisymm hux' (hmin hux'))
    exact (flip_other T x z hzx).mpr
      (hT.out ((flip_other T x u hux).mp hu)
        ((flip_other T x v hvx).mp hv) hz)

private lemma extremal_guard {x y : P} (hxy : x ⋖ y)
    (hmin : IsMin x) (hmax : IsMax y)
    {S : Set P} (hS : S.OrdConnected) :
    ((toggle y S) ∆ {x}).OrdConnected ↔ (S ∆ {x}).OrdConnected := by
  classical
  have agree (z : P) (hz : z ≠ y) : z ∈ S ↔ z ∈ toggle y S := by
    unfold toggle
    split
    · exact (flip_other S y z hz).symm
    · rfl
  constructor
  · exact transfer_extremal_cover hxy hmin hmax hS
      (fun z hz => (agree z hz).symm)
  · exact transfer_extremal_cover hxy hmin hmax (toggle_connected y hS) agree

private lemma toggle_dual (x : P) (S : Set P) :
    @toggle Pᵒᵈ _ x S = toggle x S := by
  classical
  unfold toggle
  exact ite_cond_congr (propext (@Set.ordConnected_dual P _ (S ∆ {x})))

/-- An extremal covering pair has commuting legal interval-closed toggles. -/
private lemma extremal_cover_toggles_commute {x y : P} (hxy : x ⋖ y)
    (hmin : IsMin x) (hmax : IsMax y)
    (S : Set P) (hS : S.OrdConnected) :
    toggle x (toggle y S) = toggle y (toggle x S) := by
  classical
  have hx := extremal_guard hxy hmin hmax hS
  have hy : ((toggle x S) ∆ {y}).OrdConnected ↔ (S ∆ {y}).OrdConnected := by
    have h := @extremal_guard Pᵒᵈ _ y x hxy.toDual hmax hmin S hS.dual
    constructor
    · intro hT
      have hTd := hT.dual
      rw [← toggle_dual x S] at hTd
      exact (h.mp hTd).dual
    · intro hT
      have hTd := h.mpr hT.dual
      rw [toggle_dual x S] at hTd
      exact hTd.dual
  by_cases hX : (S ∆ {x}).OrdConnected <;>
    by_cases hY : (S ∆ {y}).OrdConnected
  · have hx' := hx.mpr hX
    have hy' := hy.mpr hY
    simp only [toggle, ite_eq_left hX, ite_eq_left hY] at hx' hy' ⊢
    rw [ite_eq_left hx', ite_eq_left hy']
    rw [symmDiff_assoc, symmDiff_comm ({y} : Set P) {x}, ← symmDiff_assoc]
  · have hy' : ¬ ((S ∆ {x}) ∆ {y}).OrdConnected := by
      simpa only [toggle, ite_eq_left hX] using (mt hy.mp hY)
    simp only [toggle, ite_eq_left hX, ite_eq_right hY, ite_eq_right hy']
  · have hx' : ¬ ((S ∆ {y}) ∆ {x}).OrdConnected := by
      simpa only [toggle, ite_eq_left hY] using (mt hx.mp hX)
    simp only [toggle, ite_eq_right hX, ite_eq_left hY, ite_eq_right hx']
  · simp only [toggle, ite_eq_right hX, ite_eq_right hY]

private lemma commuting_comparable_cover {x y : P} (hxy : x < y)
    (commutes : ∀ S : Set P, S.OrdConnected →
      toggle x (toggle y S) = toggle y (toggle x S)) : x ⋖ y := by
  classical
  by_contra hcover
  obtain ⟨z, hxz, hzy⟩ := (not_covBy_iff hxy).mp hcover
  have blocked : ¬ (({x} : Set P) ∆ {y}).OrdConnected := by
    intro h
    have hx : x ∈ ({x} : Set P) ∆ {y} := by
      simp [Set.mem_symmDiff, hxy.ne]
    have hy : y ∈ ({x} : Set P) ∆ {y} := by
      simp [Set.mem_symmDiff, hxy.ne']
    have hz := h.out hx hy ⟨hxz.le, hzy.le⟩
    simp [Set.mem_symmDiff, hxz.ne', hzy.ne] at hz
  have empty_toggle (a : P) : toggle a ∅ = {a} := by
    have flip_empty : (∅ : Set P) ∆ {a} = {a} := by
      ext w
      simp [Set.mem_symmDiff]
    have legal : ((∅ : Set P) ∆ {a}).OrdConnected :=
      flip_empty.symm ▸ Set.ordConnected_singleton
    rw [toggle, ite_eq_left legal, flip_empty]
  have tx : toggle x {y} = {y} := by
    have blocked' : ¬ (({y} : Set P) ∆ {x}).OrdConnected := by
      simpa only [symmDiff_comm] using blocked
    exact ite_eq_right blocked'
  have ty : toggle y {x} = {x} := ite_eq_right blocked
  have heq := commutes ∅ Set.ordConnected_empty
  rw [empty_toggle x, empty_toggle y, tx, ty] at heq
  exact hxy.ne (Set.singleton_injective heq).symm

-- Iio y provides a convex witness without requiring a predecessor of x.
private lemma commuting_cover_min {x y : P} (hxy : x ⋖ y)
    (commutes : ∀ S : Set P, S.OrdConnected →
      toggle x (toggle y S) = toggle y (toggle x S)) : IsMin x := by
  classical
  intro z hzx
  by_contra hxz
  have hzx' : z < x := lt_of_le_not_ge hzx hxz
  let S : Set P := Set.Iio y
  let T : Set P := S \ {x}
  have hT : T.OrdConnected := by
    constructor
    intro u hu v hv w hw
    refine ⟨lt_of_le_of_lt hw.2 hv.1, ?_⟩
    intro hwx
    have hwx' : w = x := hwx
    subst w
    rcases hxy.eq_or_eq hw.2 hv.1.le with hvx | hvy
    · exact hv.2 (Set.mem_singleton_iff.mpr hvx)
    · exact hv.1.ne hvy
  have flip_x : S ∆ {x} = T := by
    ext w
    by_cases hw : w = x
    · subst w
      simp [S, T, Set.mem_symmDiff, hxy.lt]
    · simp [T, Set.mem_symmDiff, hw]
  have flip_y : S ∆ {y} = Set.Iic y := by
    ext w
    by_cases hw : w = y
    · subst w
      simp [S, Set.mem_symmDiff]
    · simp [S, Set.mem_symmDiff, hw, lt_iff_le_and_ne]
  have blocked_y : ¬ (T ∆ {y}).OrdConnected := by
    intro h
    have hz : z ∈ T ∆ {y} := by
      simp [T, S, Set.mem_symmDiff, (hzx'.trans hxy.lt), hzx'.ne,
        (hzx'.trans hxy.lt).ne]
    have hy : y ∈ T ∆ {y} := by simp [T, S, Set.mem_symmDiff]
    have hx : x ∉ T ∆ {y} := by simp [T, Set.mem_symmDiff, hxy.lt.ne]
    exact hx (h.out hz hy ⟨hzx'.le, hxy.le⟩)
  have blocked_x : ¬ ((Set.Iic y) ∆ {x}).OrdConnected := by
    intro h
    have hz : z ∈ (Set.Iic y) ∆ {x} := by
      simp [Set.mem_symmDiff, (hzx'.trans hxy.lt).le, hzx'.ne]
    have hy : y ∈ (Set.Iic y) ∆ {x} := by
      simp [Set.mem_symmDiff, hxy.lt.ne']
    have hx : x ∉ (Set.Iic y) ∆ {x} := by simp [Set.mem_symmDiff, hxy.le]
    exact hx (h.out hz hy ⟨hzx'.le, hxy.le⟩)
  have tx : toggle x S = T := by
    have legal : (S ∆ {x}).OrdConnected := flip_x.symm ▸ hT
    simpa only [toggle, ite_eq_left legal] using flip_x
  have ty : toggle y S = Set.Iic y := by
    have legal : (S ∆ {y}).OrdConnected := flip_y.symm ▸ Set.ordConnected_Iic
    simpa only [toggle, ite_eq_left legal] using flip_y
  have tyT : toggle y T = T := ite_eq_right blocked_y
  have txI : toggle x (Set.Iic y) = Set.Iic y := ite_eq_right blocked_x
  have heq := commutes S Set.ordConnected_Iio
  rw [tx, ty, txI, tyT] at heq
  have hyT : y ∈ T := heq ▸ (show y ∈ Set.Iic y from le_rfl)
  exact (lt_irrefl y) hyT.1

/-- Complete commutation criterion for the original guarded interval-closed toggle.
No finiteness or local finiteness assumption is required. -/
theorem toggles_commute_iff (x y : P) :
    (∀ S : Set P, S.OrdConnected →
      toggle x (toggle y S) = toggle y (toggle x S)) ↔
    x = y ∨ (¬ x ≤ y ∧ ¬ y ≤ x) ∨
      (IsMin x ∧ IsMax y ∧ x ⋖ y) ∨
      (IsMin y ∧ IsMax x ∧ y ⋖ x) := by
  classical
  constructor
  · intro commutes
    by_cases hxy : x = y
    · exact Or.inl hxy
    have comparable {a b : P} (hab : a < b)
        (hc : ∀ S : Set P, S.OrdConnected →
          toggle a (toggle b S) = toggle b (toggle a S)) :
        IsMin a ∧ IsMax b ∧ a ⋖ b := by
      have cover := commuting_comparable_cover hab hc
      have hmin := commuting_cover_min cover hc
      have dual_commutes : ∀ S : Set Pᵒᵈ, S.OrdConnected →
          @toggle Pᵒᵈ _ b (@toggle Pᵒᵈ _ a S) =
            @toggle Pᵒᵈ _ a (@toggle Pᵒᵈ _ b S) := by
        intro S hS
        rw [toggle_dual a S, toggle_dual b S,
          toggle_dual b (toggle a S), toggle_dual a (toggle b S)]
        exact (hc S hS.dual).symm
      exact ⟨hmin, @commuting_cover_min Pᵒᵈ _ b a cover.toDual dual_commutes, cover⟩
    by_cases hle : x ≤ y
    · exact Or.inr (Or.inr (Or.inl (comparable (lt_of_le_of_ne hle hxy) commutes)))
    by_cases hge : y ≤ x
    · exact Or.inr (Or.inr (Or.inr
        (comparable (lt_of_le_of_ne hge (Ne.symm hxy))
          (fun S hS => (commutes S hS).symm))))
    exact Or.inr (Or.inl ⟨hle, hge⟩)
  · rintro (rfl | ⟨hxy, hyx⟩ | ⟨hmin, hmax, hcover⟩ | ⟨hmin, hmax, hcover⟩) S hS
    · rfl
    · exact incomparable_toggles_commute x y hxy hyx S hS
    · exact extremal_cover_toggles_commute hcover hmin hmax S hS
    · exact (extremal_cover_toggles_commute hcover hmin hmax S hS).symm

end D5.S3.Combinatorics.Geometry.RowmotionCommutationCriterion
