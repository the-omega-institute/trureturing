/- GID: D5/S3/Combinatorics/Graph/Walks/SubtreeHelly
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/SubtreeHelly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph]
   utility: none
   digest: Finite-family Helly property for connected induced subgraphs of a tree. -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Copyright (c) 2023 Kyle Miller, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in
docs/reports/licenses/mathlib-subtree-helly/LICENSE.txt.
Original file authors: Kyle Miller; Kyle Miller, Rémi Bottinelli.
Source revision author: 8e7.
Source: https://github.com/8e7/mathlib4/tree/12cb0b6433584e454c4d4577472c4792f0dfe5c9
-/

namespace SimpleGraph

open Walk

variable {V : Type*} {G : SimpleGraph V}

private lemma preconnected_induce_iff_forall_exists_walk {s : Set V} :
    (G.induce s).Preconnected ↔
    ∀ ⦃u v⦄, u ∈ s → v ∈ s → ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∈ s := by
  refine ⟨fun hs u v hu hv => ?_,
    fun h ⟨u, hu⟩ ⟨v, hv⟩ => (h hu hv).elim fun p hp => ⟨p.induce s hp⟩⟩
  obtain ⟨p, hp⟩ := (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).mp
    (preconnected_induce_iff.mp hs) hu hv
  exact ⟨p, fun x hx => hp.1 (p.mem_verts_toSubgraph.mpr hx)⟩

namespace IsTree

/-- In a tree, the intersection of two preconnected induced subgraphs is preconnected. -/
private lemma preconnected_induce_inter {a b : Set V} (ht : G.IsTree)
    (ha : (G.induce a).Preconnected) (hb : (G.induce b).Preconnected) :
    (G.induce (a ∩ b)).Preconnected := by
  classical
  intro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨wa, hwa⟩ := preconnected_induce_iff_forall_exists_walk.mp ha hx.1 hy.1
  obtain ⟨wb, hwb⟩ := preconnected_induce_iff_forall_exists_walk.mp hb hx.2 hy.2
  have heq : wa.toPath = wb.toPath := ht.isAcyclic.path_unique _ _
  exact ⟨wa.toPath.val.induce (a ∩ b) fun z hz ↦
    ⟨hwa _ (Walk.support_toPath_subset_support _ hz),
     hwb _ (Walk.support_toPath_subset_support _ (heq ▸ hz))⟩⟩

/-- In a tree, given two connected induced subgraphs `a, b` with intersecting vertex sets, every
walk from a vertex of `a` to a vertex of `b` passes through a vertex of `a ∩ b`. -/
private lemma mem_walk_of_inter_nonempty (hT : G.IsTree) {a b : Set V}
    (ha : (G.induce a).Connected) (hb : (G.induce b).Connected) (hab : (a ∩ b).Nonempty) :
    ∀ x ∈ a, ∀ y ∈ b, ∀ w : G.Walk x y, (w.toSubgraph.verts ∩ a ∩ b).Nonempty := by
  classical
  intro x hx y hy w
  obtain ⟨m, hma, hmb⟩ := hab
  obtain ⟨wxm_g, hwxm_a⟩ := preconnected_induce_iff_forall_exists_walk.mp ha.preconnected hx hma
  obtain ⟨wmy_g, hwmy_b⟩ := preconnected_induce_iff_forall_exists_walk.mp hb.preconnected hmb hy
  let W : G.Walk x y := wxm_g.append wmy_g
  have hW_eq : W.toPath = w.toPath := hT.isAcyclic.path_unique _ _
  by_cases hy_a : y ∈ a
  · exact ⟨y, ⟨w.end_mem_verts_toSubgraph, hy_a⟩, hy⟩
  -- d is the boundary dart where d.fst ∈ a, d.snd ∉ a.
  obtain ⟨d, hd_in, hd_fst_a, hd_snd_not_a⟩ :=
    W.toPath.val.exists_boundary_dart a hx hy_a
  have hd_fst_w : d.fst ∈ w.toSubgraph.verts :=
    w.mem_verts_toSubgraph.mpr (Walk.support_toPath_subset_support w
      (hW_eq ▸ W.toPath.val.dart_fst_mem_support_of_mem_darts hd_in))
  suffices hd_fst_b : d.fst ∈ b from ⟨d.fst, ⟨hd_fst_w, hd_fst_a⟩, hd_fst_b⟩
  -- The boundary edge is on `W.toPath`, hence on one of `wxm_g`, `wmy_g`.
  obtain he_xm | he_my : s(d.fst, d.snd) ∈ wxm_g.edges ∨ s(d.fst, d.snd) ∈ wmy_g.edges := by
    rw [← List.mem_append, ← Walk.edges_append]
    exact Walk.edges_toPath_subset_edges _ (List.mem_map.mpr ⟨d, hd_in, rfl⟩)
  · exact absurd (hwxm_a _ (wxm_g.snd_mem_support_of_mem_edges he_xm)) hd_snd_not_a
  · exact hwmy_b _ (wmy_g.fst_mem_support_of_mem_edges he_my)

/-- If three subtrees have pairwise intersecting vertex sets, then there must be a vertex in all
    three sets. -/
private theorem inter_nonempty_of_pairwise_three (hT : G.IsTree) {a b c : Set V}
    (ha : (G.induce a).Connected) (hb : (G.induce b).Connected) (hc : (G.induce c).Connected)
    (hab : (a ∩ b).Nonempty) (hbc : (b ∩ c).Nonempty) (hca : (c ∩ a).Nonempty) :
    (a ∩ b ∩ c).Nonempty := by
  obtain ⟨ac, hac⟩ := hca
  obtain ⟨bc, hbc⟩ := hbc
  obtain ⟨w, hw_in_c⟩ := preconnected_induce_iff_forall_exists_walk.mp hc.preconnected
    hac.left hbc.right
  obtain ⟨v, hv⟩ : (w.toSubgraph.verts ∩ a ∩ b).Nonempty := hT.mem_walk_of_inter_nonempty ha hb hab
    ac hac.right bc hbc.left w
  have hvc : v ∈ c := hw_in_c _ (w.mem_verts_toSubgraph.mp hv.1.1)
  use v
  grind only [= Set.mem_inter_iff]

/-- Helly's property for subtrees of a tree: a nonempty finite indexed family of pairwise
intersecting connected subsets of a tree has nonempty common intersection. -/
theorem inter_nonempty_of_pairwise {ι : Type*} (hT : G.IsTree)
    {a : ι → Set V} {s : Finset ι} (hs : s.Nonempty)
    (h_conn : ∀ i ∈ s, (G.induce (a i)).Connected)
    (h_pair : ∀ i ∈ s, ∀ j ∈ s, (a i ∩ a j).Nonempty) :
    (⋂ i ∈ s, a i).Nonempty := by
  classical
  -- Convert to the logical form `∃ v, ∀ i ∈ s, v ∈ a i`.
  simp only [Set.nonempty_def, Set.mem_iInter]
  induction h_n : s.card generalizing s a with
  | zero => exact absurd h_n (Finset.card_ne_zero.mpr hs)
  | succ n ih =>
    -- Base case `#s = 1`: pick any `v ∈ a c`.
    by_cases h_one : s.card = 1
    · obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp h_one
      obtain ⟨v, hv⟩ := (h_conn c (Finset.mem_singleton_self c)).nonempty
      exact ⟨v, fun i hi ↦ (Finset.mem_singleton.mp hi).symm ▸ hv⟩
    -- Inductive case `#s ≥ 2`: pick `c ∈ s`, reduce to `s' := s.erase c` with family `a i ∩ a c`.
    obtain ⟨c, hc⟩ := hs
    set s' := s.erase c with hs'_def
    have h_card' : s'.card = n := by rw [hs'_def, Finset.card_erase_of_mem hc, h_n]; omega
    have hs' : s'.Nonempty := by rw [← Finset.card_pos, h_card']; omega
    -- For each `i ∈ s'`, `a i ∩ a c` is connected.
    have h_conn' : ∀ i ∈ s', (G.induce (a i ∩ a c)).Connected := fun i hi ↦
      have := (h_pair i (Finset.mem_of_mem_erase hi) c hc).to_subtype
      ⟨hT.preconnected_induce_inter (h_conn i (Finset.mem_of_mem_erase hi)).preconnected
        (h_conn c hc).preconnected⟩
    -- Pairwise on `s'`: a witness in `a i ∩ a j ∩ a c` (3-set Helly) lies in both `a i ∩ a c`
    -- and `a j ∩ a c`.
    have h_pair' : ∀ i ∈ s', ∀ j ∈ s', ((a i ∩ a c) ∩ (a j ∩ a c)).Nonempty := by
      intro i hi j hj
      have hi_in := Finset.mem_of_mem_erase hi
      have hj_in := Finset.mem_of_mem_erase hj
      obtain ⟨v, hv⟩ := hT.inter_nonempty_of_pairwise_three (h_conn i hi_in) (h_conn j hj_in)
        (h_conn c hc) (h_pair i hi_in j hj_in) (h_pair j hj_in c hc) (h_pair c hc i hi_in)
      exact ⟨v, ⟨hv.1.1, hv.2⟩, hv.1.2, hv.2⟩
    -- IH gives `v` with `v ∈ a i ∩ a c` for all `i ∈ s'`; so forall `i ∈ s' ∪ {c}`, `v ∈ a i`.
    obtain ⟨v, hv⟩ := ih hs' h_conn' h_pair' h_card'
    refine ⟨v, fun i hi ↦ ?_⟩
    by_cases h_eq : i = c
    · subst h_eq; obtain ⟨d, hd⟩ := hs'; exact (hv d hd).2
    · exact (hv i (Finset.mem_erase.mpr ⟨h_eq, hi⟩)).1

end IsTree

end SimpleGraph
