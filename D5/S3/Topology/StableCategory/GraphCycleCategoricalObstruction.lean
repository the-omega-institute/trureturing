/- GID: D5/S3/Topology/StableCategory/GraphCycleCategoricalObstruction
   generality: G
   mirror-B: none(waiver:consumed-by-graph-thickening-forest-cover)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite order fence fixes the rigid labels of graph cycles. -/

import D5.S3.Topology.ConnectedCategoryGraft
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Lattice.Nat

/-!
# The arboricity lower bound for the closed faces of a graph thickening

A categorical lower set has a forest as its trace on the original graph, with
an edge present exactly when its labelled top belongs to the lower set.
The argument fixes a copy of a cycle throughout any fence from the inclusion.
The application is the closed-face graph thickening in the review of Question 6.3
(https://arxiv.org/html/2609.39615v1#S6.Thmtheorem3).
-/

set_option autoImplicit false

namespace D5.S3.Topology.GraphCycleCategoricalObstruction

open ConnectedCategoryGraft (Categorical HasCategoricalCover)
open Relation (EqvGen)

variable {V P : Type*} [PartialOrder P]

/-- An adjacency gives the corresponding unordered edge. -/
def edgeOfAdj {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.edgeSet :=
  ⟨s(u, v), G.mem_edgeSet.mpr h⟩

/-- Vertex and edge labels for the cycle obstruction.
The two rigidity conditions concern all points of the ambient poset. -/
structure GraphPosetLabels (G : SimpleGraph V) (P : Type*) [PartialOrder P] where
  vertex : V → P
  vertex_injective : Function.Injective vertex
  vertex_min : ∀ v, IsMin (vertex v)
  edgeTop : G.edgeSet → P
  edge_max : ∀ e, IsMax (edgeTop e)
  vertex_le_edge : ∀ {v : V} {e : G.edgeSet}, v ∈ e.val → vertex v ≤ edgeTop e
  incident_rigid : ∀ {v : V} {e f : G.edgeSet} {x : P}, e ≠ f →
    v ∈ e.val → v ∈ f.val → vertex v ≤ x → x ≤ edgeTop e → x ≤ edgeTop f → x = vertex v
  endpoints_rigid : ∀ {u v : V} (h : G.Adj u v) {x : P},
    vertex u ≤ x → vertex v ≤ x → x ≤ edgeTop (edgeOfAdj h) → x = edgeTop (edgeOfAdj h)

/-- An indexed forest cover of the edge set of a simple graph. -/
def HasForestCover (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ H : Fin n → SimpleGraph V, (∀ i, H i ≤ G ∧ (H i).IsAcyclic) ∧
    ∀ e ∈ G.edgeSet, ∃ i, e ∈ (H i).edgeSet

/-- The minimum number of forests covering the edges of a finite graph. -/
noncomputable def arboricity (G : SimpleGraph V) [Finite V] : ℕ :=
  sInf {n | HasForestCover G n}

namespace GraphPosetLabels

variable {G : SimpleGraph V} (L : GraphPosetLabels G P)

/-- The spanning subgraph formed by the edge tops contained in the given set. -/
def trace (U : Set P) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, L.edgeTop ⟨e, h⟩ ∈ U}

theorem mem_trace_edgeSet_iff (U : Set P) (e : Sym2 V) :
    e ∈ (L.trace U).edgeSet ↔ ∃ h : e ∈ G.edgeSet, L.edgeTop ⟨e, h⟩ ∈ U := by
  rw [trace, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · exact fun h => h.1
  · rintro ⟨h, he⟩
    exact ⟨⟨h, he⟩, G.not_isDiag_of_mem_edgeSet h⟩

private theorem trace_adj_iff {U : Set P} {u v : V} :
    (L.trace U).Adj u v ↔ ∃ h : G.Adj u v, L.edgeTop (edgeOfAdj h) ∈ U :=
  (L.mem_trace_edgeSet_iff U s(u, v))

private theorem cycle_neighbors (k : ℕ) (i : Fin (k + 3)) :
    (SimpleGraph.cycleGraph (k + 3)).Adj i (i - 1) ∧
    (SimpleGraph.cycleGraph (k + 3)).Adj i (i + 1) ∧ i - 1 ≠ i + 1 := by
  have hneighbors := SimpleGraph.cycleGraph_neighborSet (n := k + 1) (v := i)
  refine ⟨?_, ?_, ?_⟩
  · rw [← SimpleGraph.mem_neighborSet, hneighbors]
    exact Set.mem_insert _ _
  · rw [← SimpleGraph.mem_neighborSet, hneighbors]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
    exact ne_of_beq_false rfl

private theorem not_categorical_of_cycle {U : Set P} (hU : IsLowerSet U) (k : ℕ)
    (cycle : (SimpleGraph.cycleGraph (k + 3)).Copy (L.trace U)) : ¬ Categorical U := by
  classical
  let I := Fin (k + 3)
  let C := SimpleGraph.cycleGraph (k + 3)
  have traceEdge (i j : I) (h : C.Adj i j) :
      ∃ hG : G.Adj (cycle i) (cycle j), L.edgeTop (edgeOfAdj hG) ∈ U :=
    (L.trace_adj_iff).mp (cycle.toHom.map_adj h)
  let graphAdj (i j : I) (h : C.Adj i j) : G.Adj (cycle i) (cycle j) :=
    (traceEdge i j h).choose
  let top (i j : I) (h : C.Adj i j) : U :=
    ⟨L.edgeTop (edgeOfAdj (graphAdj i j h)), (traceEdge i j h).choose_spec⟩
  have left_le (i j : I) (h : C.Adj i j) : L.vertex (cycle i) ≤ (top i j h).val :=
    L.vertex_le_edge (Sym2.mem_mk_left _ _)
  have right_le (i j : I) (h : C.Adj i j) : L.vertex (cycle j) ≤ (top i j h).val :=
    L.vertex_le_edge (Sym2.mem_mk_right _ _)
  let vertex (i : I) : U :=
    ⟨L.vertex (cycle i),
      hU (left_le i (i - 1) (cycle_neighbors k i).1)
        (top i (i - 1) (cycle_neighbors k i).1).property⟩
  let fixed (f : U →o P) : Prop :=
    (∀ i, f (vertex i) = (vertex i).val) ∧
    ∀ i j (h : C.Adj i j), f (top i j h) = (top i j h).val
  have step {f g : U →o P} (hfg : f ≤ g) : fixed f ↔ fixed g := by
    constructor
    · intro hf
      have fixedTop (i j : I) (h : C.Adj i j) : g (top i j h) = (top i j h).val := by
        apply (L.edge_max (edgeOfAdj (graphAdj i j h))).eq_of_ge
        exact (hf.2 i j h).symm.le.trans (OrderHom.le_def.mp hfg (top i j h))
      refine ⟨?_, fixedTop⟩
      intro i
      obtain ⟨hp, hs, hne⟩ := cycle_neighbors k i
      have edges_ne : edgeOfAdj (graphAdj i (i - 1) hp) ≠ edgeOfAdj (graphAdj i (i + 1) hs) := by
        intro he
        have hpair : s(cycle i, cycle (i - 1)) = s(cycle i, cycle (i + 1)) :=
          congrArg Subtype.val he
        exact hne (cycle.injective (Sym2.congr_right.mp hpair))
      apply L.incident_rigid edges_ne (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)
      · exact (hf.1 i).symm.le.trans (OrderHom.le_def.mp hfg (vertex i))
      · exact (g.monotone (show vertex i ≤ top i (i - 1) hp from left_le i _ hp)).trans
          (fixedTop i _ hp).le
      · exact (g.monotone (show vertex i ≤ top i (i + 1) hs from left_le i _ hs)).trans
          (fixedTop i _ hs).le
    · intro hg
      have fixedVertex (i : I) : f (vertex i) = (vertex i).val := by
        apply (L.vertex_min (cycle i)).eq_of_le
        exact (OrderHom.le_def.mp hfg (vertex i)).trans (hg.1 i).le
      refine ⟨fixedVertex, ?_⟩
      intro i j h
      apply L.endpoints_rigid (graphAdj i j h)
      · exact (fixedVertex i).symm.le.trans
          (f.monotone (show vertex i ≤ top i j h from left_le i j h))
      · exact (fixedVertex j).symm.le.trans
          (f.monotone (show vertex j ≤ top i j h from right_le i j h))
      · exact (OrderHom.le_def.mp hfg (top i j h)).trans (hg.2 i j h).le
  have fence {f g : U →o P} (h : EqvGen (· ≤ ·) f g) : fixed f ↔ fixed g := by
    induction h with
    | rel _ _ hle => exact step hle
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  rintro ⟨c, hc⟩
  have inclusion_fixed : fixed (OrderEmbedding.subtype U).toOrderHom :=
    ⟨fun _ => rfl, fun _ _ _ => rfl⟩
  have constant_fixed := (fence hc).mp inclusion_fixed
  have constant_zero : c = L.vertex (cycle 0) := constant_fixed.1 0
  have constant_one : c = L.vertex (cycle 1) := constant_fixed.1 1
  exact (show (0 : I) ≠ 1 from ne_of_beq_false rfl)
    (cycle.injective (L.vertex_injective (constant_zero.symm.trans constant_one)))

/-- Every categorical lower set has an acyclic trace. -/
theorem trace_isAcyclic {U : Set P} (hU : IsLowerSet U) (hcat : Categorical U) :
    (L.trace U).IsAcyclic := by
  refine SimpleGraph.isAcyclic_iff_free_cycleGraph.mpr ?_
  intro n hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hnk : n = k + 3 := by omega
  rw [hnk]
  rintro ⟨cycle⟩
  exact L.not_categorical_of_cycle hU k cycle hcat

include L in
/-- The same number of pieces suffice to cover the edges by forests. -/
theorem hasForestCover_of_hasCategoricalCover {n : ℕ} (h : HasCategoricalCover P n) :
    HasForestCover G n := by
  obtain ⟨U, hU, covers⟩ := h
  refine ⟨fun i => L.trace (U i), ?_, ?_⟩
  · intro i
    refine ⟨?_, L.trace_isAcyclic (hU i).1 (hU i).2⟩
    intro u v huv
    exact ((L.trace_adj_iff).mp huv).choose
  · intro e he
    obtain ⟨i, hi⟩ := covers (L.edgeTop ⟨e, he⟩)
    exact ⟨i, (L.mem_trace_edgeSet_iff (U i) e).mpr ⟨he, hi⟩⟩

end GraphPosetLabels

end D5.S3.Topology.GraphCycleCategoricalObstruction
