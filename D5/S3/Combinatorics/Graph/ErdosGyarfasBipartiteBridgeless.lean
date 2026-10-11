/- GID: D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A lexicographically minimal bipartite Erdős–Gyárfás counterexample is connected and remains connected after deletion of any edge. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import D5.S3.Combinatorics.Graph.ErdosGyarfasBridgeContraction

namespace D5.S3.Combinatorics.Graph.ErdosGyarfasBipartiteBridgeless

open SimpleGraph

/-- A cycle of length four, eight, sixteen, or a larger power of two. -/
def HasPowTwoCycle {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ ∃ k : ℕ, 2 ≤ k ∧ c.length = 2 ^ k

/-- A nonempty finite bipartite graph of minimum degree at least three with no
cycle whose length is a power of two. -/
def IsBipCounterexample {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Nonempty V ∧ G.Colorable 2 ∧ (∀ v, 3 ≤ G.degree v) ∧ ¬ HasPowTwoCycle G

/-- Minimality in the lexicographic order of the vertex and edge counts,
among counterexamples on all finite vertex types. -/
def IsMinimalBipCounterexample {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  IsBipCounterexample G ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], IsBipCounterexample H →
        (Fintype.card V < Fintype.card W ∨
          (Fintype.card V = Fintype.card W ∧ G.edgeFinset.card ≤ H.edgeFinset.card))

/-- The bipartite two-edge-connectivity assertion. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], IsMinimalBipCounterexample G →
      G.Connected ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).Connected

/-- Passing to a component preserves the counterexample conditions, so
vertex-minimality forces connectedness. -/
theorem minimal_connected {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsMinimalBipCounterexample G) : G.Connected := by
  classical
  have : Nonempty V := hG.1.1
  refine { preconnected := ?_ }
  intro u v
  by_contra huv
  let C := G.connectedComponentMk u
  let H := G.induce C.supp
  have hH : IsBipCounterexample H := by
    refine ⟨⟨⟨u, rfl⟩⟩, hG.1.2.1.of_hom (Embedding.induce C.supp).toHom, ?_, ?_⟩
    · intro x
      have hx : G.neighborSet x.val ⊆ C.supp := by
        intro y hy
        exact C.mem_supp_of_adj_mem_supp x.property hy
      simpa [H, degree_induce_of_neighborSet_subset hx] using hG.1.2.2.1 x.val
    · rintro ⟨x, c, hc, k, hk, hlen⟩
      exact hG.1.2.2.2 ⟨x.val, c.map (Embedding.induce C.supp).toHom,
        hc.map Subtype.val_injective, k, hk,
        (Walk.length_map (Embedding.induce C.supp).toHom c).trans hlen⟩
  have hv : v ∉ C.supp := by
    intro hv
    exact huv (ConnectedComponent.exact hv.symm)
  have hcard : Fintype.card C.supp < Fintype.card V := Fintype.card_subtype_lt hv
  have hmin := hG.2 C.supp H hH
  rcases hmin with hmin | ⟨hmin, _⟩ <;> omega

/-- Contracting a bridge would give a smaller bipartite counterexample. -/
theorem result : claim := by
  classical
  intro V _ _ G _ hG
  have hconn := minimal_connected G hG
  refine ⟨hconn, ?_⟩
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    have hadj : G.Adj u v := G.mem_edgeSet.mp he
    apply hconn.preconnected.connected_deleteEdges_of_not_isBridge
    intro hb
    let H := ErdosGyarfasBridgeContraction.contraction G u v
    have hH : IsBipCounterexample H := by
      refine ⟨⟨⟨u, hadj.ne⟩⟩,
        ErdosGyarfasBridgeContraction.contraction_colorable G u v hb hG.1.2.1,
        ErdosGyarfasBridgeContraction.contraction_min_degree G u v hb hadj hG.1.2.2.1,
        ?_⟩
      rintro ⟨w, p, hp, k, hk, hlen⟩
      obtain ⟨z, q, hq, hl⟩ :=
        ErdosGyarfasBridgeContraction.contraction_cycle_lift G u v hadj.ne hb p hp
      exact hG.1.2.2.2 ⟨z, q, hq, k, hk, hl.trans hlen⟩
    have hcard : Fintype.card (ErdosGyarfasBridgeContraction.ContractVertex v) <
        Fintype.card V := ErdosGyarfasBridgeContraction.contraction_card_lt v
    have hmin := hG.2 (ErdosGyarfasBridgeContraction.ContractVertex v) H hH
    rcases hmin with hmin | ⟨hmin, _⟩ <;> omega

end D5.S3.Combinatorics.Graph.ErdosGyarfasBipartiteBridgeless
