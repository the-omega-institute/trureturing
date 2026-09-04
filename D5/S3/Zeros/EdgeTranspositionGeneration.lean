/- GID: D5/S3/Zeros/EdgeTranspositionGeneration
   generality: G
   mirror-B: D5/B/S3/Zeros/EdgeTranspositionGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Edge transpositions of a finite connected graph generate every vertex permutation. -/

/- Library-search audit trail (2026-09-04):
   * D5 keyword, identifier-shape, statement-body, digestion-index, and in-flight branch
     searches found no graph-edge transposition generation theorem.
   * Pinned Mathlib provides the more general theorem
     `closure_of_isSwap_of_isPretransitive`: a finite pretransitive permutation group generated
     by transpositions is the full symmetric group. It does not connect graph reachability to
     that action, which is the bridge proved below.
   * The retired `Meta/Digestion/formalizations/` receipt tree was neither inspected nor created.

   STOPPING JUSTIFICATION: this module proves only the finite connected-graph generation claim.
   It does not assert that a particular collision or monodromy graph is connected. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Perm.ClosureSwap

namespace D5.S3.Zeros.EdgeTranspositionGeneration

open Equiv Set Subgroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The generating set consisting of the swaps across the edges of `G`. -/
def edgeTranspositions {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (Equiv.Perm V) :=
  {sigma | ∃ u v, G.Adj u v ∧ sigma = Equiv.swap u v}

private theorem edge_transposition_isSwap {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {sigma : Equiv.Perm V} (hsigma : sigma ∈ edgeTranspositions G) :
    sigma.IsSwap := by
  obtain ⟨u, v, huv, rfl⟩ := hsigma
  exact ⟨u, v, huv.ne, rfl⟩

private theorem swap_mem_closure_of_reachable {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {u v : V} (huv : G.Reachable u v) :
    Equiv.swap u v ∈ Subgroup.closure (edgeTranspositions G) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv using Relation.ReflTransGen.trans_induction_on with
  | refl vertex =>
      exact Equiv.swap_self vertex ▸ (Subgroup.closure (edgeTranspositions G)).one_mem
  | single hadj => exact Subgroup.subset_closure ⟨_, _, hadj, rfl⟩
  | trans _ _ first second =>
      exact SubmonoidClass.swap_mem_trans _ first second

/-- If a finite graph is connected, its edge transpositions generate the full symmetric group
on its vertices. -/
theorem connected_edge_transpositions_generate {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    Subgroup.closure (edgeTranspositions G) = ⊤ := by
  haveI : MulAction.IsPretransitive (Subgroup.closure (edgeTranspositions G)) V :=
    MulAction.IsPretransitive.mk fun u v => by
      refine ⟨⟨Equiv.swap u v, swap_mem_closure_of_reachable G (hG u v)⟩, ?_⟩
      exact Equiv.swap_apply_left u v
  apply closure_of_isSwap_of_isPretransitive
  intro sigma hsigma
  exact edge_transposition_isSwap G hsigma

/-- Applied to an induced connected component, the same theorem gives the componentwise form. -/
theorem edge_transpositions_generate_on_component {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (component : G.ConnectedComponent) :
    Subgroup.closure (edgeTranspositions component.toSimpleGraph) = ⊤ :=
  connected_edge_transpositions_generate component.toSimpleGraph component.connected_toSimpleGraph

#print axioms connected_edge_transpositions_generate

end D5.S3.Zeros.EdgeTranspositionGeneration
