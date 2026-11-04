/- GID: D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.claim; result=D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.result; claim=D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.claim
   digest: A connected 21-vertex ordinary-domination witness at minus four refutes the complete order-33 minimality claim. -/

/-
proof_shape: claim: definition; result: bind-only with consumed private witness and exact supplier application.
escape_witness: null; the designated external open-problem refutation is the admission basis.
admission_basis: open-problem-resolution#25239.
Direct frozen dependencies: D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.zero_of_messages.
The private witness graph, decomposition, connectivity proof and zero application are all on the live path to result.
-/

import D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.Domination.AlikhaniGriswoldMinOrderRefutation

open Finset
open D5.S3.Combinatorics.Graph.Domination.MinusFourReassembly
open DominatingSetAverage

private def witnessEdges : Finset (Fin 21 × Fin 21) := {
  (0, 5), (0, 6), (0, 7), (0, 13),
  (1, 3), (1, 4), (1, 5), (1, 6),
  (2, 3), (2, 4), (3, 13), (4, 13),
  (5, 6), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12),
  (13, 14), (13, 15), (13, 16), (16, 17), (16, 19),
  (17, 18), (19, 20) }

/-- The independently accepted ordinary graph, with exactly the listed edges. -/
private def witnessGraph : SimpleGraph (Fin 21) where
  Adj u v := (u, v) ∈ witnessEdges ∨ (v, u) ∈ witnessEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel witnessGraph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ witnessEdges ∨ _ ∈ witnessEdges))

private def branchSize : Fin 2 → ℕ := ![6, 8]

private def branchStart : Fin 2 → ℕ := ![7, 13]

private def branchLabel (i : Fin 2) (v : Fin (branchSize i)) : Fin 21 :=
  ⟨branchStart i + v.val, by fin_cases i <;> simp [branchSize, branchStart] at * <;> omega⟩

private def incidence : Fin 2 → Finset (Fin 7) := ![{0}, {0, 3, 4}]

private theorem witness_connected : witnessGraph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact (show witnessGraph.Adj 0 5 by decide).reachable.trans
      (show witnessGraph.Adj 5 1 by decide).reachable
  · exact (show witnessGraph.Adj 0 5 by decide).reachable.trans
      ((show witnessGraph.Adj 5 1 by decide).reachable.trans
        ((show witnessGraph.Adj 1 3 by decide).reachable.trans
          (show witnessGraph.Adj 3 2 by decide).reachable))
  · exact (show witnessGraph.Adj 0 5 by decide).reachable.trans
      ((show witnessGraph.Adj 5 1 by decide).reachable.trans
        (show witnessGraph.Adj 1 3 by decide).reachable)
  · exact (show witnessGraph.Adj 0 5 by decide).reachable.trans
      ((show witnessGraph.Adj 5 1 by decide).reachable.trans
        (show witnessGraph.Adj 1 4 by decide).reachable)
  · exact (show witnessGraph.Adj 0 5 by decide).reachable
  · exact (show witnessGraph.Adj 0 6 by decide).reachable
  · exact (show witnessGraph.Adj 0 7 by decide).reachable
  · exact (show witnessGraph.Adj 0 7 by decide).reachable.trans
      (show witnessGraph.Adj 7 8 by decide).reachable
  · exact (show witnessGraph.Adj 0 7 by decide).reachable.trans
      (show witnessGraph.Adj 7 9 by decide).reachable
  · exact (show witnessGraph.Adj 0 7 by decide).reachable.trans
      (show witnessGraph.Adj 7 10 by decide).reachable
  · exact (show witnessGraph.Adj 0 7 by decide).reachable.trans
      (show witnessGraph.Adj 7 11 by decide).reachable
  · exact (show witnessGraph.Adj 0 7 by decide).reachable.trans
      (show witnessGraph.Adj 7 12 by decide).reachable
  · exact (show witnessGraph.Adj 0 13 by decide).reachable
  · exact (show witnessGraph.Adj 0 13 by decide).reachable.trans
      (show witnessGraph.Adj 13 14 by decide).reachable
  · exact (show witnessGraph.Adj 0 13 by decide).reachable.trans
      (show witnessGraph.Adj 13 15 by decide).reachable
  · exact (show witnessGraph.Adj 0 13 by decide).reachable.trans
      (show witnessGraph.Adj 13 16 by decide).reachable
  · exact (show witnessGraph.Adj 0 13 by decide).reachable.trans
      ((show witnessGraph.Adj 13 16 by decide).reachable.trans
        (show witnessGraph.Adj 16 17 by decide).reachable)
  · exact (show witnessGraph.Adj 0 13 by decide).reachable.trans
      ((show witnessGraph.Adj 13 16 by decide).reachable.trans
        ((show witnessGraph.Adj 16 17 by decide).reachable.trans
          (show witnessGraph.Adj 17 18 by decide).reachable))
  · exact (show witnessGraph.Adj 0 13 by decide).reachable.trans
      ((show witnessGraph.Adj 13 16 by decide).reachable.trans
        (show witnessGraph.Adj 16 19 by decide).reachable)
  · exact (show witnessGraph.Adj 0 13 by decide).reachable.trans
      ((show witnessGraph.Adj 13 16 by decide).reachable.trans
        ((show witnessGraph.Adj 16 19 by decide).reachable.trans
          (show witnessGraph.Adj 19 20 by decide).reachable))

private def witnessTable : Fin 2 → Bool → ℤ := fun i b =>
  if b then ![972, 6912] i else ![-1024, -3328] i

private theorem witness_zero : evaluation witnessGraph (-4) = 0 := by
  let labels : (Fin 7 ⊕ (Σ i : Fin 2, Fin (branchSize i))) → Fin 21 := fun a =>
    match a with
    | .inl c => ⟨c.val, by omega⟩
    | .inr v => branchLabel v.1 v.2
  let d : Decomposition := {
    n := 21
    k := 7
    m := 2
    size := branchSize
    graph := witnessGraph
    adjDec := inferInstance
    labels := Equiv.ofBijective labels (by decide)
    root := fun i => ⟨0, by fin_cases i <;> decide⟩
    leaf := fun i => ⟨1, by fin_cases i <;> decide⟩
    incidence := incidence
    leaf_neighbors := by decide
    root_leaf_edge := by decide
    nonroot_neighbors := by decide
    core_neighbors := by decide }
  exact zero_of_messages d (-4) witnessTable (by decide) (by decide)

/-- The complete source claim: attainment at order 33 and nonvanishing at every smaller positive order. -/
def claim : Prop :=
  (∃ G : SimpleGraph (Fin 33),
      G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card = 0) ∧
    (∀ n : ℕ, 1 ≤ n → n < 33 →
      ∀ G : SimpleGraph (Fin n), G.Connected →
        ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card ≠ 0)

theorem result : ¬ claim := by
  intro h
  rcases h with ⟨_, hminimal⟩
  have hnonzero := hminimal 21 (by decide) (by decide) witnessGraph witness_connected
  apply hnonzero
  simpa [evaluation] using witness_zero

end D5.S3.Combinatorics.Graph.Domination.AlikhaniGriswoldMinOrderRefutation
