/- GID: D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unique actual path coverage earns the full support and exact uncut-edge inventories of the same supplied Hamilton cycle. -/
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualPathFamilyInventory

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Actual paths with disjoint support cannot repeat an edge, including
across different pieces. -/
theorem actual_path_partition_edges_nodup (pieces : List (Piece G))
    (hn : (pieces.flatMap fun p => p.walk.support).Nodup) :
    (pieces.flatMap fun p => p.walk.edges).Nodup := by
  obtain ⟨hpaths, hdis⟩ := List.nodup_flatMap.mp hn
  apply List.nodup_flatMap.mpr
  refine ⟨?_, hdis.imp ?_⟩
  · intro p hp
    exact (SimpleGraph.Walk.IsPath.mk' (hpaths p hp)).isTrail.edges_nodup
  · intro p q hd
    apply List.disjoint_left.mpr
    intro e he₁ he₂
    obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e
    exact List.disjoint_left.mp hd
      (p.walk.fst_mem_support_of_mem_edges he₁)
      (q.walk.fst_mem_support_of_mem_edges he₂)

/-- Exhaustion and uniqueness of actual path supports supply the exact
same-cycle inventory. A membership law for retained edges is enough
because vertex disjointness earns their multiplicity, rather than assuming
an edge-list permutation as a certificate. -/
theorem actual_path_family_cycle_inventory {n : ℕ}
    (pieces : Fin n → Piece G) (hpath : ∀ i, (pieces i).walk.IsPath)
    (hcover : ∀ v : V, ∃! i, v ∈ (pieces i).walk.support)
    {base : V} (w : G.Walk base base) (hw : w.IsHamiltonianCycle)
    (cuts : Finset (Sym2 V))
    (hedges : ∀ e, e ∈ ((List.ofFn pieces).flatMap fun p => p.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ cuts) :
    ((List.ofFn pieces).flatMap fun p => p.walk.support).Perm w.support.tail ∧
    ((List.ofFn pieces).flatMap fun p => p.walk.edges).Perm
      (w.edges.filter fun e => decide (e ∉ cuts)) := by
  classical
  have hn : ((List.ofFn pieces).flatMap fun p => p.walk.support).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨?_, List.pairwise_ofFn.mpr ?_⟩
    · intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact (hpath i).support_nodup
    · intro i j hij
      apply List.disjoint_left.mpr
      intro v hi hj
      obtain ⟨k, _, huniq⟩ := hcover v
      exact (ne_of_lt hij) ((huniq i hi).trans (huniq j hj).symm)
  have hcount (v : V) :
      ((List.ofFn pieces).flatMap fun p => p.walk.support).count v = 1 := by
    obtain ⟨i, hi, _⟩ := hcover v
    exact List.count_eq_one_of_mem hn
      (List.mem_flatMap.mpr ⟨pieces i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩)
  refine ⟨?_, ?_⟩
  · apply List.perm_iff_count.mpr
    intro v
    exact (hcount v).trans
      ((SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp hw).2 v).symm
  · apply (List.perm_ext_iff_of_nodup
      (actual_path_partition_edges_nodup (List.ofFn pieces) hn)
      (hw.isCycle.isTrail.edges_nodup.filter _)).mpr
    intro e
    simp only [hedges e, List.mem_filter, decide_eq_true_eq]

#print axioms actual_path_partition_edges_nodup
#print axioms actual_path_family_cycle_inventory

end D5.S3.Combinatorics.Graph.Walks.ActualPathFamilyInventory
