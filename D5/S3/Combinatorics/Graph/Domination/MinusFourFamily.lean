/- GID: D5/S3/Combinatorics/Graph/Domination/MinusFourFamily
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/MinusFourFamily
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.result_of_base_root; premises=D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.source_leaf,D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.source_leaf_edge,D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.parent_edge,D5/S3/Combinatorics/Graph/Domination/MinusFourFamily.parent_lower
   digest: The exact published graph and the support-replication reduction for the minus-four family question. -/

import D5.S3.Combinatorics.Graph.Domination.MinusFourReplication
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.MinusFourFamily

open Finset DominatingSetAverage LocalDominatingStemBoundReplication MinusFourReplication

/-- Factual edge data from Alikhani--Griswold, arXiv:2608.00109v1.
The independently written encoding uses the explicit graph, rather than the branch prose. -/
def sourceEdges : Finset (Fin 33 × Fin 33) := {
  (0, 1),
  (0, 3),
  (0, 4),
  (0, 12),
  (1, 2),
  (1, 12),
  (1, 18),
  (2, 3),
  (2, 6),
  (2, 8),
  (2, 10),
  (2, 18),
  (2, 21),
  (3, 21),
  (3, 24),
  (4, 5),
  (6, 7),
  (8, 9),
  (10, 11),
  (12, 13),
  (12, 14),
  (12, 15),
  (12, 16),
  (12, 17),
  (18, 19),
  (18, 20),
  (21, 22),
  (21, 23),
  (24, 25),
  (24, 26),
  (26, 27),
  (27, 28),
  (28, 29),
  (28, 31),
  (29, 30),
  (31, 32) }

/-- The actual finite simple undirected source graph on the published labels. -/
def sourceGraph : SimpleGraph (Fin 33) where
  Adj u v := (u,v) ∈ sourceEdges ∨ (v,u) ∈ sourceEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel sourceGraph.Adj := fun _ _ => inferInstanceAs
  (Decidable (_ ∈ sourceEdges ∨ _ ∈ sourceEdges))

attribute [-instance] instDecidableRelFinOfNatNatAdjSourceGraph in
private theorem source_leaf : Leaf sourceGraph (5 : Fin 33) := by
  have hn : ∀ w : Fin 33, sourceGraph.Adj 5 w ↔ w = 4 := by
    letI := instDecidableRelFinOfNatNatAdjSourceGraph
    decide
  classical
  exact SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    ⟨4, (hn 4).mpr rfl, fun w hw => (hn w).mp hw⟩

private theorem source_leaf_edge : sourceGraph.Adj (5 : Fin 33) 4 := by decide

private def parent (v : Fin 33) : Fin 33 :=
  ![0,0,1,0,0,4,2,6,2,8,2,10,0,12,12,12,12,12,1,18,18,2,21,21,3,24,24,26,27,28,29,28,31] v

private theorem parent_edge : ∀ v : Fin 33, v ≠ 0 → sourceGraph.Adj v (parent v) := by decide

private theorem parent_lower : ∀ v : Fin 33, v ≠ 0 → (parent v).val < v.val := by decide

private theorem source_connected : sourceGraph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, ?_⟩
  intro v
  have reach : ∀ (n : ℕ) (v : Fin 33), v.val = n → sourceGraph.Reachable 0 v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hzero : v = 0
      · subst v; exact SimpleGraph.Reachable.refl _
      · exact (ih (parent v).val (hv ▸ parent_lower v hzero) (parent v) rfl).trans
          (parent_edge v hzero).symm.reachable
  exact reach v.val v rfl

private theorem evaluation_iso {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (x : ℤ) : evaluation G x = evaluation H x := by
  classical
  unfold evaluation
  rw [← domSets_map e, Finset.sum_map]
  apply sum_congr rfl
  intro S _
  change x ^ S.card = x ^ (S.map e.toEquiv.toEmbedding).card
  rw [card_map]

/-- The complete unbounded-order event follows from the single exact base evaluation.
No base root is assumed elsewhere in this construction. -/
theorem result_of_base_root (hbase : evaluation sourceGraph (-4) = 0) :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card = 0 := by
  classical
  intro N
  let r := N + 1
  let R := replicated sourceGraph {4} r
  let e := Fintype.equivFin (RepVertex r (Fin 33))
  let G := R.map e
  have hn : Fintype.card (RepVertex r (Fin 33)) = 33 * r + 2 := by
    rw [replicated_card]; simp [Nat.mul_comm]
  refine ⟨Fintype.card (RepVertex r (Fin 33)), ?_, G, ?_, ?_⟩
  · rw [hn]; dsimp [r]; omega
  · exact (support_replication_connected sourceGraph 4 source_connected r).map
      (SimpleGraph.Iso.map e R).toHom e.surjective
  · change evaluation G (-4) = 0
    rw [← evaluation_iso (SimpleGraph.Iso.map e R)]
    change evaluation (replicated sourceGraph {4} r) (-4) = 0
    rw [support_replication_evaluation sourceGraph 4 5 source_leaf source_leaf_edge,
      hbase, zero_pow (by dsimp [r]; omega : r ≠ 0), mul_zero]

end D5.S3.Combinatorics.Graph.Domination.MinusFourFamily
