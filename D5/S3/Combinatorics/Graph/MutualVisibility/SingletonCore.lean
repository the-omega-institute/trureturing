/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/SingletonCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/SingletonCore
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Fewer cuts than host labels cannot separate two surviving singleton configurations. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.PairPayments

/-! The singleton core is counted in the complete source configuration graph. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open SimpleGraph
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}

private theorem singleton_pair_edges (hH : H.Connected) (x y : V) (hxy : x ≠ y) :
    (reconfiguration H).Adj ⟨{x}, visible_singleton H x⟩ ⟨{x, y}, visible_pair hH x y⟩ ∧
    (reconfiguration H).Adj ⟨{x, y}, visible_pair hH x y⟩ ⟨{y}, visible_singleton H y⟩ := by
  constructor
  · change MixedMove H {x} {x, y}
    have h := mixedMove_insert H ({x} : Finset V) (x := y) (by simpa using hxy.symm)
    simpa only [Finset.pair_comm] using h
  · change MixedMove H {x, y} {y}
    have h := mixedMove_erase H ({x, y} : Finset V) (x := x) (by simp)
    simpa [hxy] using h

theorem singleton_core (hH : H.Connected) (C : Finset (Configuration H))
    (hc : C.card < Fintype.card V) {x y : V}
    (hx : (⟨{x}, visible_singleton H x⟩ : Configuration H) ∉ C)
    (hy : (⟨{y}, visible_singleton H y⟩ : Configuration H) ∉ C) :
    CutReach (reconfiguration H) C ⟨{x}, visible_singleton H x⟩ ⟨{y}, visible_singleton H y⟩ := by
  classical
  by_contra hn
  have hxy : x ≠ y := by
    intro he
    subst y
    exact hn ⟨hx, hx, Reachable.refl _⟩
  let X : Configuration H := ⟨{x}, visible_singleton H x⟩
  let Y : Configuration H := ⟨{y}, visible_singleton H y⟩
  let O : Configuration H := ⟨∅, visible_empty H⟩
  let B : Configuration H := ⟨{x, y}, visible_pair hH x y⟩
  have hrX : CutReach (reconfiguration H) C X X := ⟨hx, hx, Reachable.refl _⟩
  have heX : (reconfiguration H).Adj X O := by
    change MixedMove H {x} ∅
    have h := mixedMove_erase H ({x} : Finset V) (x := x) (by simp)
    simpa using h
  have heY : (reconfiguration H).Adj O Y := by
    change MixedMove H ∅ {y}
    simpa using mixedMove_insert H (∅ : Finset V) (x := y) (by simp)
  have hOC : O ∈ C :=
    (cutReach_two_step_payment hrX heX heY hn).elim id (fun h => (hy h).elim)
  have hbEdges := singleton_pair_edges hH x y hxy
  have hBC : B ∈ C :=
    (cutReach_two_step_payment hrX hbEdges.1 hbEdges.2 hn).elim id (fun h => (hy h).elim)
  let Z := Finset.univ \ ({x, y} : Finset V)
  have hZ : Disjoint Z ({x, y} : Finset V) := Finset.sdiff_disjoint
  have hlocal : ∀ z ∈ Z, 1 ≤ (localCutClass C {x, y} z).card := by
    intro z hz
    have hzB := (Finset.mem_sdiff.mp hz).2
    have hzx : z ≠ x := fun h => hzB (by simp [h])
    have hzy : z ≠ y := fun h => hzB (by simp [h])
    let T : Configuration H := ⟨{z}, visible_singleton H z⟩
    apply Finset.card_pos.mpr
    by_cases hTC : T ∈ C
    · refine ⟨T, Finset.mem_filter.mpr ⟨hTC, ?_⟩⟩
      simp [T]
    · by_cases hrT : CutReach (reconfiguration H) C X T
      · have htEdges := singleton_pair_edges hH z y hzy
        have hPairC : (⟨{z, y}, visible_pair hH z y⟩ : Configuration H) ∈ C :=
          (cutReach_two_step_payment hrT htEdges.1 htEdges.2 hn).elim id (fun h => (hy h).elim)
        refine ⟨⟨{z, y}, visible_pair hH z y⟩, Finset.mem_filter.mpr ⟨hPairC, ?_⟩⟩
        simp
      · have htEdges := singleton_pair_edges hH x z hzx.symm
        have hPairC : (⟨{x, z}, visible_pair hH x z⟩ : Configuration H) ∈ C :=
          (cutReach_two_step_payment hrX htEdges.1 htEdges.2 hrT).elim id (fun h => (hTC h).elim)
        refine ⟨⟨{x, z}, visible_pair hH x z⟩, Finset.mem_filter.mpr ⟨hPairC, ?_⟩⟩
        constructor
        · simp
        · intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
          aesop
  have hinner : 2 ≤ (C.filter fun T => T.val ⊆ ({x, y} : Finset V)).card := by
    have hsub : ({O, B} : Finset (Configuration H)) ⊆ C.filter fun T => T.val ⊆ ({x, y} : Finset V) := by
      intro T hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hOC, by simp [O]⟩
      · exact Finset.mem_filter.mpr ⟨hBC, by simp [B]⟩
    have hOB : O ≠ B := by
      intro he
      have hv := congrArg Subtype.val he
      have hmem : x ∈ B.val := by simp [B]
      rw [← hv] at hmem
      simpa [O] using hmem
    have hc2 : ({O, B} : Finset (Configuration H)).card = 2 := by simp [hOB]
    rw [← hc2]
    exact Finset.card_le_card hsub
  have hbudget := joint_cut_budget C {x, y} Z hZ ∅ (by simp) (by simp) (by simp)
  have hsum : Z.card ≤ ∑ z ∈ Z, (localCutClass C {x, y} z).card := by
    calc
      Z.card = ∑ _z ∈ Z, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hlocal
  have hZcard : Z.card + 2 = Fintype.card V := by
    have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({x, y} : Finset V))
    simpa [Z, hxy] using he
  simp only [Finset.card_empty, Nat.add_zero] at hbudget
  omega

open Classical in
private theorem empty_degree (H : SimpleGraph V) :
    (reconfiguration H).degree ⟨∅, visible_empty H⟩ = Fintype.card V := by
  classical
  let O : Configuration H := ⟨∅, visible_empty H⟩
  let f : V → (reconfiguration H).neighborSet O := fun x =>
    ⟨⟨{x}, visible_singleton H x⟩, by
      change MixedMove H ∅ {x}
      simpa using mixedMove_insert H (∅ : Finset V) (x := x) (by simp)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      have hv := congrArg (fun T : (reconfiguration H).neighborSet O => T.val.val) he
      simpa [f] using hv
    · intro T
      have hm := T.property.2
      rcases hm with hm | ⟨x, y, he, _, _⟩
      · have hc1 : T.val.val.card = 1 := by
          change ((∅ : Finset V) ∆ T.val.val).card = 1 at hm
          have he : (∅ : Finset V) ∆ T.val.val = T.val.val := by
            ext z
            simp only [Finset.mem_symmDiff, Finset.notMem_empty, false_and,
              not_false_eq_true, and_true, false_or]
          rw [he] at hm
          exact hm
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
        refine ⟨x, Subtype.ext (Subtype.ext ?_)⟩
        exact hx.symm
      · simp [O] at he
  change (reconfiguration H).degree O = Fintype.card V
  calc
    (reconfiguration H).degree O = Fintype.card ((reconfiguration H).neighborSet O) :=
      (SimpleGraph.card_neighborSet_eq_degree (reconfiguration H) O).symm
    _ = Fintype.card V := (Fintype.card_congr (Equiv.ofBijective f hf)).symm

theorem minDegree_le_host_order : (reconfiguration H).minDegree ≤ Fintype.card V := by
  have h := (reconfiguration H).minDegree_le_degree ⟨∅, visible_empty H⟩
  exact h.trans (le_of_eq (empty_degree H))

end D5.S3.Combinatorics.Graph.MutualVisibility
