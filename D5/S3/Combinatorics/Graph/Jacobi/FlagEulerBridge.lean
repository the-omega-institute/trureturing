/- GID: D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge
   mirror-E: none(waiver:actual-flag-incidence-euler-bridge)
   anchors: []
   utility: none
   digest: Actual flag incidence preserves the original graph Euler genus. -/

import D5.S3.Combinatorics.Graph.Jacobi.FlagPruning
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Logic.Equiv.Sum

/-! Literal original flag pairs and the Euler count of actual incidence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.Jacobi.FlagGraph

/-- Original edges are unordered pairs of actual edge-mate flags. Their
distinct flag identities retain loops and parallel edges at rotor orbits. -/
def edgePairGraph {F : Type} (G : FlagGraph F) : SimpleGraph F where
  Adj f g := G.edge f = g
  symm := ⟨by
    intro f g h
    exact (G.edge_involutive f ▸ congrArg G.edge h).symm⟩
  loopless := ⟨fun f => G.edge_ne f⟩

/-- The Euler genus of a connected finite original flag graph. The added one
precedes natural subtraction; this also gives genus zero on a tree. -/
noncomputable def eulerGenus {F : Type} [Finite F] (G : FlagGraph F) : ℕ :=
  Nat.card G.edgePairGraph.edgeSet + 1 - Nat.card G.VertexOrbit

private noncomputable def ownerNeighborEquiv {F : Type} (G : FlagGraph F)
    (v : G.VertexOrbit) :
    G.incidence.neighborSet (.inl v) ≃ {f : F // G.vertexOf f = v} where
  toFun n := by
    rcases n with ⟨w | f, h⟩
    · exact False.elim h
    · exact ⟨f, h⟩
  invFun f := ⟨.inr f.val, f.property⟩
  left_inv n := by
    rcases n with ⟨w | f, h⟩
    · exact False.elim h
    · rfl
  right_inv _ := rfl

private noncomputable def flagNeighborEquiv {F : Type} (G : FlagGraph F)
    (f : F) : G.incidence.neighborSet (.inr f) ≃ Fin 2 := by
  classical
  exact
    { toFun n := match n.val with
        | .inl _ => 0
        | .inr _ => 1
      invFun i := if i = 0 then ⟨.inl (G.vertexOf f), rfl⟩
        else ⟨.inr (G.edge f), rfl⟩
      left_inv n := by
        rcases n with ⟨v | g, h⟩
        · apply Subtype.ext
          change Sum.inl (G.vertexOf f) = Sum.inl v
          exact congrArg Sum.inl h
        · apply Subtype.ext
          change Sum.inr (G.edge f) = Sum.inr g
          exact congrArg Sum.inr h
      right_inv i := by fin_cases i <;> simp }

private theorem incidence_edge_count {F : Type} [Finite F] (G : FlagGraph F) :
    2 * Nat.card G.incidence.edgeSet = 3 * Nat.card F := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite G.VertexOrbit
  have ho (v : G.VertexOrbit) :
      G.incidence.degree (.inl v) = Fintype.card {f : F // G.vertexOf f = v} := by
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr (G.ownerNeighborEquiv v)
  have hf (f : F) : G.incidence.degree (.inr f) = 2 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    exact (Fintype.card_congr (G.flagNeighborEquiv f)).trans (Fintype.card_fin 2)
  have hsum : (∑ v : G.VertexOrbit, Fintype.card {f : F // G.vertexOf f = v}) =
      Fintype.card F := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.vertexOf)
  have h := G.incidence.sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at h
  simp_rw [ho, hf] at h
  rw [hsum] at h
  have he : G.incidence.edgeFinset.card = Nat.card G.incidence.edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  rw [he] at h
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  simp only [Nat.card_eq_fintype_card] at h ⊢
  omega

private theorem original_edge_count {F : Type} [Finite F] (G : FlagGraph F) :
    2 * Nat.card G.edgePairGraph.edgeSet = Nat.card F := by
  classical
  let := Fintype.ofFinite F
  have hd (f : F) : G.edgePairGraph.degree f = 1 := by
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    exact ⟨G.edge f, rfl, fun g hg => (show G.edge f = g from hg).symm⟩
  have h := G.edgePairGraph.sum_degrees_eq_twice_card_edges
  simp_rw [hd] at h
  have he : G.edgePairGraph.edgeFinset.card = Nat.card G.edgePairGraph.edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  rw [he] at h
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Nat.card_eq_fintype_card] using h.symm

/-- Subdivision into actual rotor-orbit nodes and individual flag nodes
preserves the Euler cycle rank, including original loops and parallel edges. -/
theorem incidence_euler_genus {F : Type} [Finite F] (G : FlagGraph F) :
    Nat.card G.incidence.edgeSet + 1 - Nat.card G.IncidenceVertex = G.eulerGenus := by
  have hi := G.incidence_edge_count
  have he := G.original_edge_count
  have hv : Nat.card G.IncidenceVertex = Nat.card G.VertexOrbit + Nat.card F :=
    Nat.card_sum
  unfold eulerGenus
  rw [hv]
  omega

/-- On a connected finite flag graph, positive original Euler genus is
equivalent to an actual incidence cycle. Mathlib supplies the tree count. -/
theorem positive_euler_genus_iff_cycle {F : Type} [Finite F] (G : FlagGraph F)
    (hc : G.incidence.Connected) : 0 < G.eulerGenus ↔ ¬G.incidence.IsAcyclic := by
  rw [← G.incidence_euler_genus]
  have hle := hc.card_vert_le_card_edgeSet_add_one
  have ht : G.incidence.IsAcyclic ↔
      Nat.card G.incidence.edgeSet + 1 = Nat.card G.IncidenceVertex := by
    constructor
    · intro ha
      exact (SimpleGraph.isTree_iff_connected_and_card.mp ⟨hc, ha⟩).2
    · intro he
      exact (SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hc, he⟩).isAcyclic
  rw [ht]
  omega

end D5.S3.Combinatorics.Graph.Jacobi.FlagGraph
