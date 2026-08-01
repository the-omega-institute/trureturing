/- GID: D5/S1/Recurrence/CyclicNearestReturn
   generality: G
   mirror-B: D5/B/S1/Recurrence/CyclicNearestReturn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cyclic successor and predecessor as mutually inverse nearest returns. -/

import Mathlib.Data.Finset.Max
import Mathlib.Order.Fin.Basic

namespace D5.S1.Recurrence.CyclicNearestReturn

/-- The first point of `S` strictly to the right of `x`, wrapping to the minimum. -/
def cyclicSucc {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (x : α) : α :=
  if h : (S.filter (x < ·)).Nonempty then
    (S.filter (x < ·)).min' h
  else
    S.min' hS

/-- The first point of `S` strictly to the left of `x`, wrapping to the maximum. -/
def cyclicPred {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (x : α) : α :=
  if h : (S.filter (· < x)).Nonempty then
    (S.filter (· < x)).max' h
  else
    S.max' hS

/-- Cyclic nearest returns stay in the finite carrier, are mutual inverses there,
and select the closest point in either direction, including both wrap cases. -/
theorem cyclic_nearest_return_spec {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) :
    (∀ x ∈ S, cyclicSucc S hS x ∈ S) ∧
    (∀ x ∈ S, cyclicPred S hS x ∈ S) ∧
    (∀ x ∈ S, cyclicPred S hS (cyclicSucc S hS x) = x) ∧
    (∀ x ∈ S, cyclicSucc S hS (cyclicPred S hS x) = x) ∧
    (∀ x ∈ S, ∀ y ∈ S, x < y → ¬ y < cyclicSucc S hS x) ∧
    (∀ x ∈ S, ∀ y ∈ S, y < x → ¬ cyclicPred S hS x < y) ∧
    cyclicSucc S hS (S.max' hS) = S.min' hS ∧
    cyclicPred S hS (S.min' hS) = S.max' hS := by
  have succ_mem : ∀ x ∈ S, cyclicSucc S hS x ∈ S := by
    intro x hx
    unfold cyclicSucc
    split
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
    · exact S.min'_mem hS
  have pred_mem : ∀ x ∈ S, cyclicPred S hS x ∈ S := by
    intro x hx
    unfold cyclicPred
    split
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ _)).1
    · exact S.max'_mem hS
  have succ_nearest :
      ∀ x ∈ S, ∀ y ∈ S, x < y → ¬ y < cyclicSucc S hS x := by
    intro x hx y hy hxy
    unfold cyclicSucc
    split
    · rename_i hAbove
      intro hySucc
      have hSuccLe : (S.filter (x < ·)).min' hAbove ≤ y :=
        Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hy, hxy⟩)
      exact (not_lt_of_ge hSuccLe) hySucc
    · rename_i hAbove
      exact (hAbove ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩).elim
  have pred_nearest :
      ∀ x ∈ S, ∀ y ∈ S, y < x → ¬ cyclicPred S hS x < y := by
    intro x hx y hy hyx
    unfold cyclicPred
    split
    · rename_i hBelow
      intro hPredY
      have hYLe : y ≤ (S.filter (· < x)).max' hBelow :=
        Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hy, hyx⟩)
      exact (not_lt_of_ge hYLe) hPredY
    · rename_i hBelow
      exact (hBelow ⟨y, Finset.mem_filter.mpr ⟨hy, hyx⟩⟩).elim
  have pred_succ : ∀ x ∈ S, cyclicPred S hS (cyclicSucc S hS x) = x := by
    intro x hx
    by_cases hAbove : (S.filter (x < ·)).Nonempty
    · let z := (S.filter (x < ·)).min' hAbove
      have hzData := Finset.mem_filter.mp (Finset.min'_mem _ hAbove)
      have hBelow : (S.filter (· < z)).Nonempty :=
        ⟨x, Finset.mem_filter.mpr ⟨hx, hzData.2⟩⟩
      rw [cyclicSucc, dif_pos hAbove, cyclicPred, dif_pos hBelow]
      apply (Finset.max'_eq_iff _ _ x).mpr
      refine ⟨Finset.mem_filter.mpr ⟨hx, hzData.2⟩, ?_⟩
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyS, hyz⟩
      by_contra hyx
      have hxy : x < y := lt_of_not_ge hyx
      have hzy : z ≤ y :=
        Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hyS, hxy⟩)
      exact (not_lt_of_ge hzy) hyz
    · have hxMax : S.max' hS = x := by
        apply (Finset.max'_eq_iff _ _ x).mpr
        refine ⟨hx, ?_⟩
        intro y hy
        exact le_of_not_gt fun hxy =>
          hAbove ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
      have hBelow : ¬(S.filter (· < S.min' hS)).Nonempty := by
        rintro ⟨y, hy⟩
        rcases Finset.mem_filter.mp hy with ⟨hyS, hyMin⟩
        exact (not_lt_of_ge (Finset.min'_le _ _ hyS)) hyMin
      rw [cyclicSucc, dif_neg hAbove, cyclicPred, dif_neg hBelow, hxMax]
  have succ_pred : ∀ x ∈ S, cyclicSucc S hS (cyclicPred S hS x) = x := by
    intro x hx
    by_cases hBelow : (S.filter (· < x)).Nonempty
    · let z := (S.filter (· < x)).max' hBelow
      have hzData := Finset.mem_filter.mp (Finset.max'_mem _ hBelow)
      have hAbove : (S.filter (z < ·)).Nonempty :=
        ⟨x, Finset.mem_filter.mpr ⟨hx, hzData.2⟩⟩
      rw [cyclicPred, dif_pos hBelow, cyclicSucc, dif_pos hAbove]
      apply (Finset.min'_eq_iff _ _ x).mpr
      refine ⟨Finset.mem_filter.mpr ⟨hx, hzData.2⟩, ?_⟩
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyS, hzy⟩
      by_contra hyx
      have hyx' : y < x := lt_of_not_ge hyx
      have hyz : y ≤ z :=
        Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hyS, hyx'⟩)
      exact (not_lt_of_ge hyz) hzy
    · have hxMin : S.min' hS = x := by
        apply (Finset.min'_eq_iff _ _ x).mpr
        refine ⟨hx, ?_⟩
        intro y hy
        exact le_of_not_gt fun hyx =>
          hBelow ⟨y, Finset.mem_filter.mpr ⟨hy, hyx⟩⟩
      have hAbove : ¬(S.filter (S.max' hS < ·)).Nonempty := by
        rintro ⟨y, hy⟩
        rcases Finset.mem_filter.mp hy with ⟨hyS, hMaxY⟩
        exact (not_lt_of_ge (Finset.le_max' _ _ hyS)) hMaxY
      rw [cyclicPred, dif_neg hBelow, cyclicSucc, dif_neg hAbove, hxMin]
  have succ_wrap : cyclicSucc S hS (S.max' hS) = S.min' hS := by
    rw [cyclicSucc, dif_neg]
    rintro ⟨y, hy⟩
    rcases Finset.mem_filter.mp hy with ⟨hyS, hMaxY⟩
    exact (not_lt_of_ge (Finset.le_max' _ _ hyS)) hMaxY
  have pred_wrap : cyclicPred S hS (S.min' hS) = S.max' hS := by
    rw [cyclicPred, dif_neg]
    rintro ⟨y, hy⟩
    rcases Finset.mem_filter.mp hy with ⟨hyS, hyMin⟩
    exact (not_lt_of_ge (Finset.min'_le _ _ hyS)) hyMin
  exact ⟨succ_mem, pred_mem, pred_succ, succ_pred, succ_nearest,
    pred_nearest, succ_wrap, pred_wrap⟩

example :
    let S : Finset (Fin 5) := {0, 2, 4}
    let hS : S.Nonempty := by decide
    cyclicSucc S hS 0 = 2 ∧ cyclicSucc S hS 4 = 0 ∧
      cyclicPred S hS 0 = 4 ∧ cyclicPred S hS 4 = 2 := by
  decide

end D5.S1.Recurrence.CyclicNearestReturn
