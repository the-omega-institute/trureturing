/- GID: D5/S3/Combinatorics/Graph/Walks/EdgeMengerCertificates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/EdgeMengerCertificates
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.LineGraph, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity]
   utility: none
   digest: Finite edge-deletion resilience is equivalent to pairwise edge-disjoint path certificates. -/

import D5.S3.Combinatorics.Graph.Walks.MengerCertificates
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in
 docs/reports/licenses/menger-hamiltonian-LICENSE.txt.
Authors: Juan Pablo Traverso Gianini

Adapted source: jtraverso/menger-hamiltonian,
commit 35c5f684f9bfbd244bd0999ce725623ab571adb6,
MengerHamilton/MengerCore.lean: lift_to_lineGraph, walk_in_edge,
lower_from_lineGraph; MengerHamilton/Menger.lean: isEdgeReachable_iff.
The source attributes Menger's theorem to Diestel, Graph Theory, Theorem 3.3.1,
second proof (Boehme, Goering, Harant). No originality is claimed.
The receiver reuses the public finite vertex-Menger certificate directly.
Retire this port when this repository's own adopted Mathlib pin supplies the
entire equivalent finite edge theorem and all consumers migrate lawfully.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates

open SimpleGraph

variable {V : Type*}

/-- A walk of `G` starting at a vertex of an edge `e` gives a walk in the line graph from `e`
through the edges of the walk. -/
private lemma lift_to_lineGraph {G : SimpleGraph V} :
    ∀ {w z : V} (p : G.Walk w z) (e : G.edgeSet), w ∈ (e : Sym2 V) →
      ∃ e' : G.edgeSet, z ∈ (e' : Sym2 V) ∧ ∃ q : G.lineGraph.Walk e e',
        ∀ f ∈ q.support, f = e ∨ (f : Sym2 V) ∈ p.edges
  | _, _, .nil, e, he => ⟨e, he, .nil, by simp⟩
  | _, _, .cons (v := w') h p, e, he => by
    obtain ⟨e', he', q, hq⟩ := lift_to_lineGraph p ⟨s(_, w'), h⟩ (Sym2.mem_mk_right _ _)
    by_cases heq : e = ⟨s(_, w'), h⟩
    · subst heq
      refine ⟨e', he', q, fun f hf => ?_⟩
      rcases hq f hf with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by simp [h1])
    · have hadj : G.lineGraph.Adj e ⟨s(_, w'), h⟩ :=
        lineGraph_adj_iff_exists.2 ⟨heq, _, he, Sym2.mem_mk_left _ _⟩
      refine ⟨e', he', .cons hadj q, fun f hf => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact Or.inl rfl
      rcases hq f hf with h1 | h1
      · exact Or.inr (by simp [h1])
      · exact Or.inr (by simp [h1])

private lemma walk_in_edge {G : SimpleGraph V} (e : G.edgeSet) {z m : V} (hz : z ∈ (e : Sym2 V))
    (hm : m ∈ (e : Sym2 V)) : ∃ r : G.Walk z m, ∀ f ∈ r.edges, f = (e : Sym2 V) := by
  by_cases h : z = m
  · subst h
    exact ⟨.nil, by simp⟩
  · have he : (e : Sym2 V) = s(z, m) := (Sym2.mem_and_mem_iff h).1 ⟨hz, hm⟩
    have hadj : G.Adj z m := by rw [← G.mem_edgeSet, ← he]; exact e.2
    exact ⟨.cons hadj .nil, by simp [he]⟩

/-- A walk in the line graph gives a walk of `G` using only edges in its support. -/
private lemma lower_from_lineGraph {G : SimpleGraph V} :
    ∀ {e f : G.edgeSet} (q : G.lineGraph.Walk e f) {z z' : V}, z ∈ (e : Sym2 V) →
      z' ∈ (f : Sym2 V) → ∃ r : G.Walk z z', ∀ g ∈ r.edges, ∃ e'' ∈ q.support, g = (e'' : Sym2 V)
  | _, _, .nil, _, _, hz, hz' => by
    obtain ⟨r, hr⟩ := walk_in_edge _ hz hz'
    exact ⟨r, fun g hg => ⟨_, Walk.start_mem_support _, hr g hg⟩⟩
  | e, _, .cons h q, _, _, hz, hz' => by
    obtain ⟨-, m, hm1, hm2⟩ := lineGraph_adj_iff_exists.1 h
    obtain ⟨r1, hr1⟩ := walk_in_edge e hz hm1
    obtain ⟨r2, hr2⟩ := lower_from_lineGraph q hm2 hz'
    refine ⟨r1.append r2, fun g hg => ?_⟩
    rw [Walk.edges_append, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ⟨e, by simp, hr1 g hg⟩
    · obtain ⟨e'', he'', rfl⟩ := hr2 g hg
      exact ⟨e'', by simp [he''], rfl⟩


/-- **Menger's theorem, edge form.** In a finite graph, `u` and `v` remain connected after the
deletion of any fewer than `k` edges if and only if there are `k` pairwise edge-disjoint paths
from `u` to `v`. -/
theorem isEdgeReachable_iff [Finite V] (G : SimpleGraph V) (k : ℕ) (u v : V) :
    G.IsEdgeReachable k u v ↔
      ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
        ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges := by
  constructor
  · intro h
    by_cases huv : u = v
    · subst huv
      exact ⟨fun _ => Walk.nil, fun _ => Walk.IsPath.nil, fun _ _ _ => by simp⟩
    classical
    have := Fintype.ofFinite V
    obtain ⟨X, hX, a, b, P, hP, hd⟩ := (MengerCertificates.exists_separator_paths_and_weak_duality G.lineGraph
      (Finset.univ.filter (fun e : G.edgeSet => u ∈ (e : Sym2 V)))
      (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V)))).1
    have hk : k ≤ X.card := by
      by_contra hlt
      push Not at hlt
      have hS : (Subtype.val '' (X : Set G.edgeSet)).encard < k := by
        rw [Subtype.val_injective.encard_image, Set.encard_coe_eq_coe_finsetCard]
        exact_mod_cast hlt
      obtain ⟨q⟩ := h hS
      obtain ⟨w, hadj, q', -⟩ := Walk.exists_eq_cons_of_ne huv q
      rw [deleteEdges_adj] at hadj
      obtain ⟨e', he'v, r, hr⟩ := lift_to_lineGraph (q'.mapLe (G.deleteEdges_le _))
        ⟨s(u, w), hadj.1⟩ (Sym2.mem_mk_right _ _)
      obtain ⟨x, hxX, hxr⟩ := hX ⟨s(u, w), hadj.1⟩ (by simp) e' (by simp [he'v]) r
      rcases hr x hxr with rfl | hx
      · exact hadj.2 ⟨_, hxX, rfl⟩
      · rw [Walk.edges_mapLe_eq_edges] at hx
        have := q'.edges_subset_edgeSet hx
        rw [edgeSet_deleteEdges] at this
        exact this.2 ⟨x, hxX, rfl⟩
    have hlow : ∀ i, ∃ r : G.Walk u v, ∀ g ∈ r.edges, ∃ e'' ∈ (P i).support, g = (e'' : Sym2 V) :=
      fun i => lower_from_lineGraph (P i) (by simpa using (hP i).1) (by simpa using (hP i).2.1)
    choose r hr using hlow
    refine ⟨fun i => (r (Fin.castLE hk i)).bypass, fun i => Walk.bypass_isPath _,
      fun i j hij g hg hg' => ?_⟩
    obtain ⟨e1, he1, rfl⟩ := hr _ g (Walk.edges_bypass_subset_edges _ hg)
    obtain ⟨e2, he2, he12⟩ := hr _ _ (Walk.edges_bypass_subset_edges _ hg')
    have := Subtype.ext he12
    subst this
    exact hd _ _ (fun h => hij (Fin.castLE_injective hk h)) _ he1 he2
  · rintro ⟨p, hp, hd⟩ S hS
    by_contra hreach
    have hmeet : ∀ i, ∃ e ∈ (p i).edges, e ∈ S := by
      intro i
      by_contra h
      push Not at h
      exact hreach ⟨(p i).toDeleteEdges S h⟩
    choose f hf hfS using hmeet
    have hinj : Set.InjOn f Set.univ := by
      intro i _ j _ hij
      by_contra hne
      exact hd i j hne (hf i) (by rw [hij]; exact hf j)
    have := Set.encard_le_encard_of_injOn (fun i _ => hfS i) hinj
    simp only [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
    exact absurd hS (not_lt.2 this)

end D5.S3.Combinatorics.Graph.Walks.EdgeMengerCertificates
