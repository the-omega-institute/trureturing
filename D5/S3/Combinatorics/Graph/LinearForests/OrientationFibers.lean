/- GID: D5/S3/Combinatorics/Graph/LinearForests/OrientationFibers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/OrientationFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Actual full-cycle permutations over labelled undirected cycles. -/

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import D5.S3.Combinatorics.Graph.PlanarMatching.RotationFaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
namespace D5.S3.Combinatorics.Graph.LinearForests.OrientationFibers
open SimpleGraph Equiv

variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem walk_permutation {C : SimpleGraph V} {a : V}
    (p : C.Walk a a) (hp : p.IsCycle) (hall : ∀ v, v ∈ p.support) :
    ∃ σ : Perm V, σ.IsCycleOn Set.univ ∧
      ∀ d : C.Dart, d ∈ p.darts ↔ σ d.fst = d.snd := by
  classical
  let l := p.support.dropLast
  have hn : l.Nodup := hp.nodup_dropLast_support
  have hl : l.length = p.length := by simp [l]
  have hm (v : V) : v ∈ l := by
    apply p.tail_support_perm_dropLast_support.mem_iff.mp
    have hv := hall v
    rw [← p.cons_tail_support, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact p.end_mem_tail_support hp.not_nil
    · exact hv
  have hnext (i : ℕ) (hi : i < p.length) :
      l.formPerm (p.getVert i) = p.getVert (i + 1) := by
    have h := List.formPerm_apply_getElem l hn i (by omega)
    have hget (j : ℕ) (hj : j < p.length) :
        l[j]'(by omega) = p.getVert j := by
      simp only [l, List.getElem_dropLast]
      exact p.support_getElem_eq_getVert _
    rw [hget i hi] at h
    by_cases hj : i + 1 < p.length
    · simpa only [hl, Nat.mod_eq_of_lt hj, hget (i + 1) hj] using h
    · have he : i + 1 = p.length := by omega
      simpa only [hl, he, Nat.mod_self, hget 0 (by omega),
        Walk.getVert_zero, Walk.getVert_length] using h
  have hd (d : C.Dart) (h : d ∈ p.darts) : l.formPerm d.fst = d.snd := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    rw [p.getElem_darts]
    exact hnext i (by simpa using hi)
  have hcy : l.formPerm.IsCycle := List.isCycle_formPerm hn (by have := hp.three_le_length; omega)
  have hs : {v | l.formPerm v ≠ v} = Set.univ := by
    have h := List.support_formPerm_of_nodup' l hn (by
      intro v hv
      have := hp.three_le_length
      have : l.length = 1 := by rw [hv]; rfl
      omega)
    rw [h]
    ext v
    simp [hm v]
  refine ⟨l.formPerm, hs ▸ hcy.isCycleOn, fun d => ⟨hd d, fun h => ?_⟩⟩
  obtain ⟨e, he, hef⟩ := List.mem_map.mp (show d.fst ∈ p.darts.map (·.fst) by
    rw [p.map_fst_darts]
    exact hm d.fst)
  have hes : e.snd = d.snd := (hd e he).symm.trans (hef ▸ h)
  have hed : e = d := Dart.ext _ _ (Prod.ext hef hes)
  exact hed ▸ he

private theorem raw_cycle_permutation (C : SimpleGraph V) [DecidableRel C.Adj]
    (hc : C.Connected) (hd : ∀ v, C.degree v = 2) :
    ∃ σ : Perm V, σ.IsCycleOn Set.univ ∧
      ∀ x y, C.Adj x y ↔ σ x = y ∨ σ y = x := by
  classical
  have hcycles : C.IsCycles := by
    intro v _
    simpa only [Set.ncard_eq_toFinset_card', ← C.neighborFinset_def,
      C.card_neighborFinset_eq_degree] using hd v
  obtain ⟨a⟩ := hc.nonempty
  have hne : (C.neighborSet a).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    simpa only [Set.ncard_eq_toFinset_card', ← C.neighborFinset_def,
      C.card_neighborFinset_eq_degree, hd] using (by decide : 2 ≠ 0))
  obtain ⟨p, hp, hverts⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := C.connectedComponentMk a) (by simp [ConnectedComponent.mem_supp_iff]) hne
  have hall (v : V) : v ∈ p.support := by
    rw [← Walk.mem_verts_toSubgraph, hverts, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact hc v a
  obtain ⟨σ, hσ, hσd⟩ := walk_permutation p hp hall
  refine ⟨σ, hσ, fun x y => ?_⟩
  constructor
  · intro h
    have he : s(x,y) ∈ p.edges := by
      exact Walk.mem_edges_toSubgraph.mp
        ((hp.adj_toSubgraph_iff_of_isCycles hcycles
          (p.mem_verts_toSubgraph.mpr (hall x)) y).mpr h)
    rw [p.edges_eq_map_darts] at he
    obtain ⟨d, hd, he⟩ := List.mem_map.mp he
    have hh := (Sym2.eq_iff).mp he
    rcases hh with hh | hh
    · left
      have h := (hσd d).mp hd
      simpa only [Dart.edge, Sym2.mk] using h
    · right
      have h := (hσd d).mp hd
      grind [Dart.edge]
  · rintro (h | h)
    · obtain ⟨d, hd, hdx⟩ := List.mem_map.mp (show x ∈ p.darts.map (·.fst) by
        rw [p.map_fst_darts]
        apply p.tail_support_perm_dropLast_support.mem_iff.mp
        have hv := hall x
        rw [← p.cons_tail_support, List.mem_cons] at hv
        exact hv.elim (fun e => e ▸ p.end_mem_tail_support hp.not_nil) id)
      have hdy : d.snd = y := ((hσd d).mp hd).symm.trans (hdx ▸ h)
      simpa only [hdx, hdy] using d.adj
    · exact C.symm (by
        obtain ⟨d, hd, hdy⟩ := List.mem_map.mp (show y ∈ p.darts.map (·.fst) by
          rw [p.map_fst_darts]
          apply p.tail_support_perm_dropLast_support.mem_iff.mp
          have hv := hall y
          rw [← p.cons_tail_support, List.mem_cons] at hv
          exact hv.elim (fun e => e ▸ p.end_mem_tail_support hp.not_nil) id)
        have hdx : d.snd = x := ((hσd d).mp hd).symm.trans (hdy ▸ h)
        simpa only [hdy, hdx] using d.adj)

end D5.S3.Combinatorics.Graph.LinearForests.OrientationFibers
