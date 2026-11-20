/- GID: D5/S3/Combinatorics/Graph/LeaflessDartTour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LeaflessDartTour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonbacktracking all-edge tours in finite connected graphs without leaves. -/

module

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-! All-edge nonbacktracking walks in finite connected simple graphs without leaves. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.LeaflessDartTour

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem exists_cycle_of_not_acyclic {H : SimpleGraph V} (h : ¬ H.IsAcyclic) :
    ∃ x, ∃ c : H.Walk x x, c.IsCycle := by
  simpa only [IsAcyclic, not_forall, not_not] using h

private theorem deleted_cycle_of_bridge [Finite V] (a : G.Dart)
    (hleaf : ∀ x, (G.neighborSet x).ncard ≠ 1) (hb : G.IsBridge a.edge) :
    ∃ x, (G.deleteEdges {a.edge}).Reachable a.snd x ∧
      ∃ c : (G.deleteEdges {a.edge}).Walk x x, c.IsCycle := by
  classical
  let := Fintype.ofFinite V
  let H := G.deleteEdges {a.edge}
  let C := H.connectedComponentMk a.snd
  have hv : a.snd ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
  have hu : a.fst ∉ C.supp := by
    intro hm
    exact (isBridge_iff.mp hb) (C.reachable_of_mem_supp hm hv)
  have hother : ∃ z, G.Adj a.snd z ∧ z ≠ a.fst := by
    by_contra! hn
    exact hleaf a.snd ((ncard_neighborSet ..).trans
      (degree_eq_one_iff_existsUnique_adj.mpr ⟨a.fst, a.adj.symm, hn⟩))
  obtain ⟨z, hz, hzu⟩ := hother
  have hzH : H.Adj a.snd z := by
    refine deleteEdges_adj.mpr ⟨hz, ?_⟩
    simp only [Set.mem_singleton_iff, Dart.edge, Sym2.eq_iff]
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact a.snd_ne_fst h
    · exact hzu h
  have hzC := C.mem_supp_of_adj_mem_supp hv hzH
  let : Nontrivial C := ⟨⟨⟨a.snd, hv⟩, ⟨z, hzC⟩, fun h =>
    hz.ne (congrArg Subtype.val h)⟩⟩
  let := Fintype.ofFinite C
  have hdegree (x : C) (hx : x.val ≠ a.snd) : (H.induce C.supp).degree x ≠ 1 := by
    have hsame := degree_induce_of_neighborSet_subset (G := H) (s := C.supp) (v := x)
      (fun _ hy => C.mem_supp_of_adj_mem_supp x.property hy)
    simp only [← ncard_neighborSet] at hsame ⊢
    rw [hsame]
    have heq : H.neighborSet x.val = G.neighborSet x.val := by
      ext y
      simp only [mem_neighborSet, H, deleteEdges_adj, Set.mem_singleton_iff, Dart.edge]
      refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
      rw [Sym2.eq_iff]
      rintro (⟨he, _⟩ | ⟨he, _⟩)
      · exact hu (he ▸ x.property)
      · exact hx he
    simpa only [heq] using hleaf x.val
  have hcyc : ¬ (H.induce C.supp).IsAcyclic := by
    intro hacyc
    have htree : (H.induce C.supp).IsTree := ⟨C.connected_toSimpleGraph, hacyc⟩
    obtain ⟨x, y, hxy, hx, hy⟩ := htree.exists_ne_and_degree_eq_one
    by_cases hxv : x.val = a.snd
    · exact hdegree y (fun hyv => hxy (Subtype.ext (hxv.trans hyv.symm))) hy
    · exact hdegree x hxv hx
  obtain ⟨x, c, hc⟩ := exists_cycle_of_not_acyclic hcyc
  exact ⟨x.val, C.reachable_of_mem_supp hv x.property, c.map C.toSimpleGraph_hom,
    hc.map Subtype.val_injective⟩

private theorem deleted_cycle [Finite V] (a : G.Dart) (hconn : G.Connected)
    (hleaf : ∀ x, (G.neighborSet x).ncard ≠ 1) (hcycles : ¬ G.IsCycles) :
    ∃ x, (G.deleteEdges {a.edge}).Reachable a.snd x ∧
      ∃ c : (G.deleteEdges {a.edge}).Walk x x, c.IsCycle := by
  classical
  by_cases hb : G.IsBridge a.edge
  · exact deleted_cycle_of_bridge a hleaf hb
  let := Fintype.ofFinite V
  let : Nontrivial V := ⟨⟨a.fst, a.snd, a.fst_ne_snd⟩⟩
  let H := G.deleteEdges {a.edge}
  have hH : H.Connected := hconn.preconnected.connected_deleteEdges_of_not_isBridge hb
  have hmin (x : V) : 2 ≤ G.degree x := by
    have hp : 0 < G.degree x :=
      (G.degree_pos_iff_exists_adj x).mpr (hconn.preconnected.exists_adj_of_nontrivial x)
    have hn : G.degree x ≠ 1 := by simpa only [ncard_neighborSet] using hleaf x
    omega
  have hcyc : ¬ H.IsAcyclic := by
    intro hacyc
    have htree : H.IsTree := ⟨hH, hacyc⟩
    have hc := htree.card_edgeFinset
    have he : H.edgeFinset = G.edgeFinset.erase a.edge := by
      ext e
      rw [Finset.mem_erase, mem_edgeFinset, mem_edgeFinset]
      simp [H, edgeSet_deleteEdges, and_comm]
    rw [he, Finset.card_erase_of_mem (mem_edgeFinset.mpr a.edge_mem)] at hc
    have hcard : G.edgeFinset.card = Fintype.card V := by
      have hp : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨_, mem_edgeFinset.mpr a.edge_mem⟩
      omega
    have hsum := G.sum_degrees_eq_twice_card_edges
    rw [hcard] at hsum
    apply hcycles
    intro x _
    rw [ncard_neighborSet]
    by_contra hn
    have hlt : 2 < G.degree x := by have := hmin x; omega
    have hstrict : (∑ _y : V, 2) < ∑ y : V, G.degree y :=
      Finset.sum_lt_sum (fun y _ => hmin y) ⟨x, Finset.mem_univ _, hlt⟩
    rw [hsum, Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, mul_comm 2] at hstrict
    exact (lt_irrefl _ hstrict)
  obtain ⟨x, c, hc⟩ := exists_cycle_of_not_acyclic hcyc
  exact ⟨x, hH a.snd x, c, hc⟩


private theorem closed_detour {v z : V} (reach : G.Reachable v z) (c : G.Walk z z)
    (hc : c.IsCycle) :
    ∃ p : G.Walk v v, ¬ p.Nil ∧ p.edges.IsChain (· ≠ ·) := by
  classical
  let candidate := fun n : ℕ =>
    ∃ x ∈ c.support, ∃ p : G.Walk v x, p.IsPath ∧ p.length = n
  obtain ⟨q, hq⟩ := reach.exists_isPath
  have hex : ∃ n, candidate n := ⟨q.length, z, c.start_mem_support, q, hq, rfl⟩
  obtain ⟨x, hx, p, hp, hlen⟩ := Nat.find_spec hex
  let cycle := c.rotate x hx
  have hcycle := hc.rotate hx
  have hcn : cycle.edges ≠ [] := Walk.edges_eq_nil.not.mpr hcycle.not_nil
  have hcc : cycle.edges.IsChain (· ≠ ·) := hcycle.isTrail.edges_nodup.isChain
  by_cases hn : p.Nil
  · have h : v = x := hn.eq
    subst v
    exact ⟨cycle, hcycle.not_nil, hcc⟩
  have hpen : p.penultimate ∉ cycle.support := by
    intro hm
    have hm' := (Walk.mem_support_rotate_iff c x hx).mp hm
    have hshort : candidate p.dropLast.length :=
      ⟨_, hm', p.dropLast, hp.dropLast, rfl⟩
    have hmin := Nat.find_min' hex hshort
    have hadd := Walk.length_dropLast_add_one hn
    omega
  have hstem : s(p.penultimate, x) ∉ cycle.edges :=
    fun hm => hpen (cycle.fst_mem_support_of_mem_edges hm)
  have hpn : p.edges ≠ [] := Walk.edges_eq_nil.not.mpr hn
  have hlast (e : Sym2 V) (he : e ∈ p.edges.getLast?) : e = s(p.penultimate, x) := by
    rw [List.getLast?_eq_getLast_of_ne_nil hpn] at he
    exact (by simpa using he : s(p.penultimate, x) = e).symm
  have hpc : (p.edges ++ cycle.edges).IsChain (· ≠ ·) :=
    hp.isTrail.edges_nodup.isChain.append hcc (by
      intro e he f hf hef
      rw [hlast e he] at hef
      exact hstem (hef ▸ List.mem_of_mem_head? hf))
  refine ⟨(p.append cycle).append p.reverse, ?_, ?_⟩
  · rw [Walk.not_nil_iff_lt_length, Walk.length_append, Walk.length_append]
    have hpos : 0 < cycle.length := Walk.not_nil_iff_lt_length.mp hcycle.not_nil
    omega
  · rw [Walk.edges_append, Walk.edges_append, Walk.edges_reverse]
    apply hpc.append (List.nodup_reverse.mpr hp.isTrail.edges_nodup).isChain
    intro e he f hf hef
    rw [List.getLast?_append_of_ne_nil _ hcn] at he
    rw [List.head?_reverse] at hf
    rw [hlast f hf] at hef
    exact hstem (hef ▸ List.mem_of_mem_getLast? he)

private theorem avoids_deleted_edge (a : G.Dart) {u v : V}
    (p : (G.deleteEdges {a.edge}).Walk u v) :
    a.edge ∉ p.edges := by
  intro h
  have hm := p.edges_subset_edgeSet h
  simp [edgeSet_deleteEdges] at hm

private def dartStep (d e : G.Dart) : Prop := G.DartAdj d e ∧ d.edge ≠ e.edge

private theorem dartStep_iff {l : List G.Dart} :
    l.IsChain dartStep ↔ l.IsChain G.DartAdj ∧ (l.map Dart.edge).IsChain (· ≠ ·) := by
  rw [List.isChain_map]
  induction l with
  | nil => simp
  | cons d l ih =>
    cases l with
    | nil => simp
    | cons e tail =>
      simp only [List.isChain_cons_cons, ih, dartStep]
      tauto

private theorem reverse_dart_chain [Finite V] (a : G.Dart) (hconn : G.Connected)
    (hleaf : ∀ x, (G.neighborSet x).ncard ≠ 1) (hcycles : ¬ G.IsCycles) :
    ∃ l : List G.Dart, (a :: (l ++ [a.symm])).IsChain dartStep := by
  obtain ⟨z, hr, c, hc⟩ := deleted_cycle a hconn hleaf hcycles
  obtain ⟨p, hp, hchain⟩ := closed_detour hr c hc
  let q := p.mapLe (deleteEdges_le _)
  have hq : q.edges = p.edges := p.edges_mapLe_eq_edges _
  have hend : a.edge ∉ q.edges := by rw [hq]; exact avoids_deleted_edge a p
  have hn : q.edges ≠ [] := by rw [hq]; exact Walk.edges_eq_nil.not.mpr hp
  refine ⟨q.darts, dartStep_iff.mpr ⟨?_, ?_⟩⟩
  · rcases a with ⟨⟨u, v⟩, h⟩
    have hc := ((q.cons h).concat h.symm).isChain_dartAdj_darts
    simpa only [Walk.darts_concat, Walk.darts_cons, List.concat_eq_append, List.cons_append,
      Dart.symm, Prod.swap] using hc
  · simp only [List.map_cons, List.map_append, Dart.edge_symm,
      ← Walk.edges_eq_map_darts]
    rw [List.isChain_cons]
    constructor
    · intro e he heq
      rw [List.head?_append_of_ne_nil _ hn] at he
      exact hend (heq ▸ List.mem_of_mem_head? he)
    · apply List.IsChain.append (l₂ := [a.edge]) (by rwa [hq]) (by simp)
      intro e he f hf hef
      have hf' : a.edge = f := by simpa using hf
      rw [← hf'] at hef
      exact hend (hef ▸ List.mem_of_mem_getLast? he)

private theorem splice {a b : G.Dart} {l r : List G.Dart}
    (hl : (a :: l).IsChain dartStep) (hb : (a :: l).getLast? = some b)
    (hr : (b :: r).IsChain dartStep) :
    (a :: (l ++ r)).IsChain dartStep := by
  have hne : a :: l ≠ [] := List.cons_ne_nil _ _
  have hlast : (a :: l).getLast hne = b :=
    Option.some.inj ((List.getLast?_eq_getLast_of_ne_nil hne).symm.trans hb)
  have hsplit : (a :: l).dropLast ++ [b] = a :: l := by
    rw [← hlast, List.dropLast_append_getLast hne]
  have h := List.IsChain.append_overlap (l₁ := (a :: l).dropLast) (l₂ := [b])
    (l₃ := r) (hsplit.symm ▸ hl) hr (by simp)
  rw [hsplit] at h
  exact h

private theorem refined_chain [Finite V] (hconn : G.Connected)
    (hleaf : ∀ x, (G.neighborSet x).ncard ≠ 1) (hcycles : ¬ G.IsCycles)
    {a b : G.Dart} {l : List G.Dart} (hl : (a :: l).IsChain G.DartAdj)
    (hb : (a :: l).getLast? = some b) :
    ∃ r, (a :: r).IsChain dartStep ∧ (a :: r).getLast? = some b := by
  induction l generalizing a with
  | nil =>
    exact ⟨[], by simp, hb⟩
  | cons d tail ih =>
    obtain ⟨hadj, ht⟩ := List.isChain_cons_cons.mp hl
    obtain ⟨r, hr, hlast⟩ := ih ht (by simpa using hb)
    have hd : ∃ s, (a :: s).IsChain dartStep ∧ (a :: s).getLast? = some d := by
      by_cases he : d.edge = a.edge
      · have hd : d = a.symm := by
          rcases (dart_edge_eq_iff d a).mp he with h | h
          · subst d
            exact (a.snd_ne_fst hadj).elim
          · exact h
        subst d
        obtain ⟨s, hs⟩ := reverse_dart_chain a hconn hleaf hcycles
        exact ⟨s ++ [a.symm], hs, by rw [← List.cons_append, List.getLast?_concat]⟩
      · exact ⟨[d], by simpa [dartStep, ne_comm] using And.intro hadj he, by simp⟩
    obtain ⟨s, hs, hlastS⟩ := hd
    refine ⟨s ++ r, splice hs hlastS hr, ?_⟩
    cases r with
    | nil => simpa [hlastS] using hlast
    | cons e es =>
      rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      simpa using hlast

private theorem chain_between [Finite V] (hconn : G.Connected)
    (hleaf : ∀ x, (G.neighborSet x).ncard ≠ 1) (hcycles : ¬ G.IsCycles)
    (a b : G.Dart) :
    ∃ l, (a :: l).IsChain dartStep ∧ (a :: l).getLast? = some b := by
  obtain ⟨p⟩ := hconn a.snd b.fst
  apply refined_chain hconn hleaf hcycles (l := p.darts ++ [b])
  · have h := ((p.cons a.adj).concat b.adj).isChain_dartAdj_darts
    simpa only [Walk.darts_concat, Walk.darts_cons, List.concat_eq_append, List.cons_append] using h
  · rw [← List.cons_append, List.getLast?_concat]

private theorem visit_darts {a b : G.Dart}
    (between : ∀ d e : G.Dart, ∃ l, (d :: l).IsChain dartStep ∧
      (d :: l).getLast? = some e) (targets : List G.Dart) :
    ∃ l, (a :: l).IsChain dartStep ∧ (a :: l).getLast? = some b ∧
      ∀ d ∈ targets, d ∈ a :: l := by
  induction targets generalizing a with
  | nil =>
    obtain ⟨l, hl, hlast⟩ := between a b
    exact ⟨l, hl, hlast, by simp⟩
  | cons d targets ih =>
    obtain ⟨s, hs, hsd⟩ := between a d
    obtain ⟨r, hr, hrb, hcov⟩ := ih (a := d)
    have hmem : d ∈ a :: s := List.mem_of_mem_getLast? (by simp [hsd])
    refine ⟨s ++ r, splice hs hsd hr, ?_, ?_⟩
    · cases r with
      | nil => simpa [hsd] using hrb
      | cons x xs =>
        rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
        simpa using hrb
    · intro e he
      rw [List.mem_cons] at he
      rw [← List.cons_append, List.mem_append]
      rcases he with rfl | he
      · exact Or.inl hmem
      · rcases List.mem_cons.mp (hcov e he) with rfl | he
        · exact Or.inl hmem
        · exact Or.inr he

private theorem cycle_tour [Finite V] (a : G.Dart) (hconn : G.Connected)
    (hcycles : G.IsCycles) :
    ∃ (w : G.Walk a.fst a.snd) (hw : ¬ w.Nil),
      2 ≤ w.length ∧ w.firstDart hw = a ∧ w.lastDart hw = a ∧
        w.edges.IsChain (· ≠ ·) ∧ w.edgeSet = G.edgeSet := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨p, hp⟩ := (hcycles.reachable_deleteEdges a.adj).symm.exists_isPath
  let q := p.mapLe (deleteEdges_le _)
  have havoid : a.edge ∉ q.edges := by
    rw [show q.edges = p.edges from p.edges_mapLe_eq_edges _]
    exact avoids_deleted_edge a p
  let c := q.cons a.adj
  have hc : c.IsCycle := (Walk.cons_isCycle_iff q a.adj).mpr ⟨hp.mapLe _, havoid⟩
  have hq : ¬ q.Nil := q.not_nil_of_ne a.snd_ne_fst
  let w := c.concat a.adj
  have hlen : 2 ≤ w.length := by
    have := hc.three_le_length
    rw [Walk.length_concat]
    omega
  have hw := Walk.not_nil_iff_lt_length.mpr (by omega : 0 < w.length)
  have hdarts : w.darts = a :: (q.darts ++ [a]) := by
    simp only [w, c, Walk.darts_concat, Walk.darts_cons, List.concat_eq_append,
      List.cons_append]
  refine ⟨w, hw, hlen, ?_, ?_, ?_, ?_⟩
  · rw [Walk.firstDart_eq_head_darts, ← Option.some_inj, ← List.head?_eq_some_head, hdarts]
    rfl
  · rw [Walk.lastDart_eq_getLast_darts, ← Option.some_inj,
      ← List.getLast?_eq_getLast_of_ne_nil, hdarts, ← List.cons_append, List.getLast?_concat]
  · rw [Walk.edges_concat, List.concat_eq_append]
    apply hc.isTrail.edges_nodup.isChain.append (l₂ := [a.edge]) (by simp)
    intro e he f hf hef
    have hf' : a.edge = f := by simpa using hf
    have hne : q.edges ≠ [] := Walk.edges_eq_nil.not.mpr hq
    have he' : e ∈ q.edges.getLast? := by
      rw [show c.edges = [a.edge] ++ q.edges by rfl,
        List.getLast?_append_of_ne_nil _ hne] at he
      exact he
    rw [← hf'] at hef
    exact havoid (hef ▸ List.mem_of_mem_getLast? he')
  · refine Set.Subset.antisymm w.edgeSet_subset_edgeSet ?_
    rintro ⟨u, v⟩ huv
    have hclosed (x : V) (hx : x ∈ c.toSubgraph.verts) (y : V) (hxy : G.Adj x y) :=
      (hc.adj_toSubgraph_iff_of_isCycles hcycles hx y).mpr hxy
    have hu := (hconn a.fst u).mem_subgraphVerts hclosed c.start_mem_verts_toSubgraph
    have he := Walk.adj_toSubgraph_iff_mem_edges.mp (hclosed u hu v huv)
    change s(u, v) ∈ w.edges
    rw [Walk.edges_concat, List.concat_eq_append]
    exact List.mem_append_left _ he

/-- Every dart of a finite connected graph without leaves begins and ends a
nonbacktracking walk that traverses every edge and has length at least two. -/
public theorem exists_nonbacktracking_all_edge_tour [Finite V] (hconn : G.Connected)
    (hleaf : ∀ v, (G.neighborSet v).ncard ≠ 1) (a : G.Dart) :
    ∃ (w : G.Walk a.fst a.snd) (hw : ¬ w.Nil),
      2 ≤ w.length ∧ w.firstDart hw = a ∧ w.lastDart hw = a ∧
        w.edges.IsChain (· ≠ ·) ∧ w.edgeSet = G.edgeSet := by
  classical
  by_cases hcycles : G.IsCycles
  · exact cycle_tour a hconn hcycles
  let := Fintype.ofFinite V
  obtain ⟨l, hl, hlast, hcov⟩ := visit_darts (a := a) (b := a)
    (chain_between hconn hleaf hcycles) (Finset.univ : Finset G.Dart).toList
  have hne : a :: l ≠ [] := List.cons_ne_nil _ _
  have ha : (a :: l).getLast hne = a :=
    Option.some.inj ((List.getLast?_eq_getLast_of_ne_nil hne).symm.trans hlast)
  let w := Walk.ofDarts (a :: l) hne (dartStep_iff.mp hl).1
  have hd : w.darts = a :: l := Walk.darts_ofDarts _ _
  have hlen : 2 ≤ w.length := by
    have hm := hcov a.symm (by simp)
    have htail : a.symm ∈ l := (List.mem_cons.mp hm).resolve_left a.symm_ne
    have hp := List.length_pos_of_mem htail
    rw [Walk.length_ofDarts, List.length_cons]
    omega
  have hedges : w.edges.IsChain (· ≠ ·) := by
    rw [Walk.edges_ofDarts]
    exact (dartStep_iff.mp hl).2
  have hcover : w.edgeSet = G.edgeSet := by
    refine Set.Subset.antisymm w.edgeSet_subset_edgeSet ?_
    rintro ⟨u, v⟩ huv
    let d : G.Dart := ⟨(u, v), huv⟩
    have hm := hcov d (by simp)
    change d.edge ∈ w.edges
    rw [Walk.edges_ofDarts]
    exact List.mem_map_of_mem hm
  let q : G.Walk a.fst a.snd := w.copy rfl (congrArg (fun d : G.Dart => d.snd) ha)
  have hqd : q.darts = a :: l := (w.darts_copy _ _).trans hd
  have hq : ¬ q.Nil := Walk.darts_eq_nil.not.mp (hqd.symm ▸ hne)
  refine ⟨q, hq, ?_, ?_, ?_, ?_, ?_⟩
  · exact (w.length_copy _ _).symm ▸ hlen
  · rw [Walk.firstDart_eq_head_darts, ← Option.some_inj, ← List.head?_eq_some_head, hqd]
    rfl
  · rw [Walk.lastDart_eq_getLast_darts, ← Option.some_inj,
      ← List.getLast?_eq_getLast_of_ne_nil, hqd]
    exact hlast
  · exact (w.edges_copy _ _).symm ▸ hedges
  · exact (w.edgeSet_copy _ _).trans hcover

/--
info: 'D5.S3.Combinatorics.Graph.LeaflessDartTour.exists_nonbacktracking_all_edge_tour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_nonbacktracking_all_edge_tour

end D5.S3.Combinatorics.Graph.LeaflessDartTour
