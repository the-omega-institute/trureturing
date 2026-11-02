/- GID: D5/S3/Topology/WeavingStateGraphBridge
   generality: G
   mirror-B: D5/B/S3/Topology/WeavingStateGraphBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: The canonical graph state polynomial is the actual mixed-circle state sum, -/

import D5.S3.Topology.WeavingEulerDefect
import D5.S3.Topology.WeavingCoefficientConsumer

/-! The canonical graph state polynomial is the actual mixed-circle state sum,
via the full spanning-graph isomorphism and finite-state reindexing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Topology.WeavingStateGraphBridge
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Polynomial

open D5.S3.Topology.WeavingDiagramPorts
open D5.S3.Topology.WeavingMixedComponents
open D5.S3.Topology.WeavingReferenceIncidence
open D5.S3.Topology.WeavingReferenceDegree
open D5.S3.Topology.WeavingEulerDefect
open D5.S3.Topology.WeavingCoefficientConsumer
open D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate

private def edgeSetGraphEdgeEquiv {v : ℕ} (G : SimpleGraph (Fin v)) :
    G.edgeSet ≃ graphEdge G :=
  Equiv.subtypeEquivRight (fun e => by
    induction e using Sym2.inductionOn with
    | hf u v => exact Iff.rfl)

/-- The retained crossing-edge bijection, followed by the actual vertex order
and the graph supplier's precise edge-subtype identification. -/
def crossingGraphEdgeEquiv (P : Parameters) (p : ℕ) (hp : p < 2) :
    Crossing P ≃ graphEdge (orderedGraph P p hp) :=
  (crossingEdgeEquiv P p hp).trans
    ((edgeEquiv (orderedGraphIso P p hp)).trans
      (edgeSetGraphEdgeEquiv (orderedGraph P p hp)))

@[simp] theorem crossingGraphEdgeEquiv_val (P : Parameters) (p : ℕ) (hp : p < 2)
    (z : Crossing P) :
    (crossingGraphEdgeEquiv P p hp z).val =
      s(vertexOrder P p hp (edgeEnds P p z.1 z.2).1,
        vertexOrder P p hp (edgeEnds P p z.1 z.2).2) := rfl

def stateEdges (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) : Finset (graphEdge (orderedGraph P p hp)) :=
  S.map (crossingGraphEdgeEquiv P p hp).toEmbedding

@[simp] theorem stateEdges_card (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) : (stateEdges P p hp S).card = S.card := by
  simp [stateEdges]

theorem stateGraph_adj_iff (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (u v : Circle P p) :
    (graphOfState (orderedGraph P p hp) (stateEdges P p hp S)).Adj
        (vertexOrder P p hp u) (vertexOrder P p hp v) ↔
      (referenceGraph P p hp S).Adj u v := by
  classical
  unfold graphOfState
  rw [SimpleGraph.fromEdgeSet_adj]
  change (s(vertexOrder P p hp u, vertexOrder P p hp v) ∈
      (stateEdges P p hp S).image (fun e => e.val) ∧
      vertexOrder P p hp u ≠ vertexOrder P p hp v) ↔ _
  constructor
  · rintro ⟨he, _⟩
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp he
    rw [crossingGraphEdgeEquiv_val] at heq
    refine ⟨z, hz, ?_⟩
    rcases Sym2.eq_iff.mp heq with heq | heq
    · exact Or.inl ⟨((vertexOrder P p hp).injective heq.1).symm,
        ((vertexOrder P p hp).injective heq.2).symm⟩
    · exact Or.inr ⟨((vertexOrder P p hp).injective heq.2).symm,
        ((vertexOrder P p hp).injective heq.1).symm⟩
  · rintro ⟨z, hz, h⟩
    refine ⟨Finset.mem_image.mpr ⟨crossingGraphEdgeEquiv P p hp z,
      Finset.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩, ?_⟩
    · rw [crossingGraphEdgeEquiv_val]
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    · intro he
      exact (referenceGraph P p hp S).ne_of_adj ⟨z, hz, h⟩
        ((vertexOrder P p hp).injective he)

/-- An isomorphism on the FULL vertex types, not only their supports. -/
def stateGraphIso (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    referenceGraph P p hp S ≃g
      graphOfState (orderedGraph P p hp) (stateEdges P p hp S) where
  toEquiv := vertexOrder P p hp
  map_rel_iff' := by
    intro u v
    exact stateGraph_adj_iff P p hp S u v

theorem graphRank_stateEdges (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    graphRank (orderedGraph P p hp) (stateEdges P p hp S) = q P p hp S := by
  have hc := Nat.card_congr (stateGraphIso P p hp S).connectedComponentEquiv
  unfold graphRank q
  rw [← hc, vertexCount_eq_circle_card P p hp]

/-- The canonical graph exponent is precisely one less than the actual
mixed-circle count. Its Nat representation is justified by positivity. -/
theorem stateExponent_eq_mixed (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    stateExponent (vertexCount P p)
        (graphRank (orderedGraph P p hp) (stateEdges P p hp S))
        (stateEdges P p hp S).card
        (graph_rank_bounds (vertexCount_pos P p hp) (orderedGraph P p hp)
          (stateEdges P p hp S)).2.2 =
      Nat.card (MixedCircle P p S) - 1 := by
  have hi : stateExponentInteger (vertexCount P p)
      (graphRank (orderedGraph P p hp) (stateEdges P p hp S))
      (stateEdges P p hp S).card = (Nat.card (MixedCircle P p S) : ℤ) - 1 := by
    unfold stateExponentInteger
    rw [graphRank_stateEdges, stateEdges_card, vertexCount_eq_circle_card P p hp]
    exact (mixed_circle_exponent P p hp S).2.symm
  have he := (stateExponent_cast_eq_integer
    (graph_rank_bounds (vertexCount_pos P p hp) (orderedGraph P p hp)
      (stateEdges P p hp S)).2.2).trans hi
  have hpos := mixed_card_pos P p S
  omega

/-- Actual mixed-circle state term. q is the proved spanning-quotient rank. -/
def mixedStateTerm (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) : ℤ[X] :=
  Polynomial.C ((-1 : ℤ) ^ S.card) * Polynomial.X ^ q P p hp S *
    (1 + Polynomial.X) ^ (Nat.card (MixedCircle P p S) - 1)

def mixedStatePolynomial (P : Parameters) (p : ℕ) (hp : p < 2) : ℤ[X] :=
  ∑ S : Finset (Crossing P), mixedStateTerm P p hp S

theorem graph_stateTerm_eq_mixed (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    stateTerm (vertexCount P p) (graphRank (orderedGraph P p hp))
        (fun T => (graph_rank_bounds (vertexCount_pos P p hp)
          (orderedGraph P p hp) T).2.2) (stateEdges P p hp S) =
      mixedStateTerm P p hp S := by
  unfold stateTerm mixedStateTerm
  rw [stateExponent_eq_mixed, graphRank_stateEdges, stateEdges_card]

/-- Paid finite-state reindexing, not a polynomial-identity hypothesis. -/
theorem graphStatePolynomial_eq_mixed (P : Parameters) (p : ℕ) (hp : p < 2) :
    graphStatePolynomial (vertexCount_pos P p hp) (orderedGraph P p hp) =
      mixedStatePolynomial P p hp := by
  classical
  unfold graphStatePolynomial statePolynomial mixedStatePolynomial
  symm
  apply Fintype.sum_equiv (Equiv.finsetCongr (crossingGraphEdgeEquiv P p hp))
  intro S
  exact (graph_stateTerm_eq_mixed P p hp S).symm

end
end D5.S3.Topology.WeavingStateGraphBridge
