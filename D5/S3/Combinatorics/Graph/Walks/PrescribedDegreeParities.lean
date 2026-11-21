/- GID: D5/S3/Combinatorics/Graph/Walks/PrescribedDegreeParities
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/PrescribedDegreeParities
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite connected graph admits exactly the vertex degree parities with zero total in ZMod 2. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities

open Finset Matrix SimpleGraph Sym2

variable {V : Type*} [Fintype V] [Fintype (Sym2 V)] [DecidableEq V]

omit [Fintype V] in
private theorem edge_column {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (adj : G.Adj u v) :
    (G.incMatrix (ZMod 2)).mulVec (Pi.single s(u,v) 1) =
      Pi.single u 1 + Pi.single v 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp only [Matrix.col_apply, SimpleGraph.incMatrix_apply', SimpleGraph.mk'_mem_incidenceSet_iff,
    adj, true_and, Pi.add_apply]
  by_cases h₁ : x = u <;> by_cases h₂ : x = v
  · exact (adj.ne (h₁.symm.trans h₂)).elim
  all_goals
    simp [h₁, h₂, adj.ne, adj.ne.symm]

omit [Fintype V] in
private theorem walk_boundary {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (walk : G.Walk u v) :
    ∃ x : Sym2 V → ZMod 2,
      (G.incMatrix (ZMod 2)).mulVec x = Pi.single u 1 + Pi.single v 1 := by
  induction walk with
  | @nil a =>
    refine ⟨0, ?_⟩
    rw [Matrix.mulVec_zero]
    funext w
    change 0 = (Pi.single a 1 : V → ZMod 2) w + (Pi.single a 1 : V → ZMod 2) w
    exact ((by decide : ∀ b : ZMod 2, b + b = 0) _).symm
  | @cons a b c adj rest induction =>
    obtain ⟨x, hx⟩ := induction
    refine ⟨Pi.single s(a,b) 1 + x, ?_⟩
    rw [Matrix.mulVec_add, edge_column adj, hx]
    funext w
    have same := (by decide : ∀ t : ZMod 2, t + t = 0) ((Pi.single b 1 : V → ZMod 2) w)
    simp only [Pi.add_apply]
    calc
      _ = (Pi.single a 1 : V → ZMod 2) w + (Pi.single c 1 : V → ZMod 2) w + ((Pi.single b 1 : V → ZMod 2) w + (Pi.single b 1 : V → ZMod 2) w) := by ac_rfl
      _ = _ := by rw [same, add_zero]

private theorem connected_parity_incidence (G : SimpleGraph V) [DecidableRel G.Adj]
    (conn : G.Connected) (d : V → ZMod 2) (zeroSum : (∑ v, d v) = 0) :
    ∃ x : Sym2 V → ZMod 2, (G.incMatrix (ZMod 2)).mulVec x = d := by
  classical
  let root := conn.nonempty.some
  have walks (v : V) := walk_boundary (conn.preconnected v root).some
  choose coeff hcoeff using walks
  refine ⟨∑ v, d v • coeff v, ?_⟩
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, hcoeff, smul_add, sum_add_distrib, ← sum_smul, zeroSum, zero_smul,
    add_zero]
  funext v
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single v]
  · simp
  · intro u _ ne
    simp [Pi.single_eq_of_ne ne.symm]
  · simp

/-- Prescribed degree parities on a connected finite graph are realizable by a spanning
subgraph exactly when their sum in the two-element field is zero. -/
open Classical in
theorem exact_parity_subgraph (G : SimpleGraph V) (conn : G.Connected) (d : V → ZMod 2) :
    (∃ H : SimpleGraph V, H ≤ G ∧ ∀ v, (Nat.card (H.neighborSet v) : ZMod 2) = d v) ↔ ∑ v, d v = 0 := by
  constructor
  · rintro ⟨H, _, parities⟩
    simp_rw [← parities, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
    rw [← Nat.cast_sum, H.sum_degrees_eq_twice_card_edges, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  · intro total
    obtain ⟨x, hx⟩ := connected_parity_incidence G conn d total
    let H := fromEdgeSet {e | e ∈ G.edgeSet ∧ x e = 1}
    have edges (e : Sym2 V) : e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∧ x e = 1 := by
      simp only [H, edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq]
      exact ⟨And.left, fun h => ⟨h, G.not_isDiag_of_mem_edgeSet h.1⟩⟩
    refine ⟨H, edgeSet_subset_edgeSet.mp (fun e he => ((edges e).mp he).1), fun v => ?_⟩
    have rowDegree : (Nat.card (H.neighborSet v) : ZMod 2) = ∑ e, H.incMatrix (ZMod 2) v e := by
      rw [H.sum_incMatrix_apply (R := ZMod 2) (a := v), Nat.card_eq_fintype_card,
        card_neighborSet_eq_degree]
    rw [rowDegree, ← congrFun hx v]
    unfold Matrix.mulVec dotProduct
    apply sum_congr rfl
    intro e _
    have incidence : e ∈ H.incidenceSet v ↔ e ∈ G.incidenceSet v ∧ x e = 1 := by
      simp only [incidenceSet, Set.mem_ofPred_eq, edges]
      tauto
    simp only [incMatrix_apply', incidence]
    by_cases hit : e ∈ G.incidenceSet v
    · rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (x e) with h | h
      · simp [hit, h, zero_ne_one]
      · simp [hit, h]
    · simp [hit]

end D5.S3.Combinatorics.Graph.Walks.PrescribedDegreeParities
