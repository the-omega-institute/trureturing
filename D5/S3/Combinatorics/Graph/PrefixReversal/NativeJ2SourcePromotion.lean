/- Candidate source-promotion companion. This file has not yet been
   kernel checked and is not part of the narrow parent delivery.
   The goal is to derive the original P opening inventories from one
   retained RawSeedFor, not choose a replacement child witness. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
import D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open private pChildIndex outer_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private map_filtered_complement from
  D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open private actual_joint_split_cut_inventory from
  D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory

/-- The actual ordinary opening in the parent retains the original P
supplier's full joint support and exactly its original uncut edges.
The old joint cuts are restored before removing this particular supplier
edge; each inventory refers to W.P, W.oldP and W.paths simultaneously. -/
theorem native_j2_original_p_opening_inventory {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    let O := outerFrame F A u hbase
    let j := pChildIndex F A u hbase
    let opening := (W.paths j).piece.walk
    let jointEdges := (List.ofFn W.P.seed.joint).flatMap fun p => p.walk.edges
    let jointSupport := (List.ofFn W.P.seed.joint).flatMap fun p => p.walk.support
    let cut := s(rightPort O (2 + j.val), leftPort O (2 + j.val))
    (opening.support.map Subtype.val).Perm (jointSupport.map Subtype.val) ∧
      (opening.edges.map (Sym2.map Subtype.val)).Perm
        ((W.P.seed.walk.edges.map (Sym2.map Subtype.val)).filter
          fun e => decide (e ≠ cut)) ∧
      (opening.edges.map (Sym2.map Subtype.val)).Perm
        (((jointEdges ++ W.P.seed.H.toList ++ W.P.seed.K.toList).map
          (Sym2.map Subtype.val)).filter fun e => decide (e ≠ cut)) := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let j := pChildIndex F A u hbase
  have hj : 0 < j.val := by change 0 < A.length; omega
  let hBO := outer_base_bound F A u hbase hA
  let q := (W.paths j).piece.walk
  let e := s(ordinaryRight (by omega : 3 ≤ m) O hBO j hj,
    ordinaryLeft (by omega : 3 ≤ m) O hBO j hj)
  have hcut (f) : f ∈ q.edges ↔ f ∈ W.oldP.cycle.walk.edges ∧ f ≠ e := by
    have h := W.ordinaryInventory j hj f
    rw [W.oldPAttached] at h
    exact h
  have hs : q.support.Perm W.oldP.cycle.walk.support.tail := by
    apply List.perm_iff_count.mpr
    intro x
    rw [(W.paths j).hamiltonian x]
    exact (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp
      W.oldP.cycle.hamiltonian).2 x |>.symm
  have he : q.edges.Perm (W.oldP.cycle.walk.edges.filter fun f => decide (f ≠ e)) := by
    apply (List.perm_ext_iff_of_nodup
      (W.paths j).hamiltonian.isPath.isTrail.edges_nodup
      (W.oldP.cycle.hamiltonian.isCycle.isTrail.edges_nodup.filter _)).mpr
    intro f
    simp only [List.mem_filter, decide_eq_true_eq]
    exact hcut f
  have hrawSupport : W.oldP.cycle.walk.support.map Subtype.val =
      W.P.seed.walk.support.map Subtype.val := by
    have h := congrArg (fun z => z.support.map Subtype.val) W.oldP.mappedWalk
    simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.map_map, Function.comp_def] using h
  have hrawEdges : W.oldP.cycle.walk.edges.map (Sym2.map Subtype.val) =
      W.P.seed.walk.edges.map (Sym2.map Subtype.val) := by
    have h := congrArg (fun z => z.edges.map (Sym2.map Subtype.val)) W.oldP.mappedWalk
    simpa only [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map,
      List.map_map, Function.comp_def, Sym2.map_map] using h
  have htail : W.oldP.cycle.walk.support.tail.map Subtype.val =
      W.P.seed.walk.support.tail.map Subtype.val := by
    simpa only [List.map_tail] using congrArg List.tail hrawSupport
  have hsraw : (q.support.map Subtype.val).Perm
      (W.P.seed.walk.support.tail.map Subtype.val) := by
    rw [← htail]
    exact hs.map Subtype.val
  have hsJoint := W.P.seed.partitions.joint_partition.support.map Subtype.val
  have hefilter : (W.oldP.cycle.walk.edges.filter fun f => decide (f ≠ e)).map
      (Sym2.map Subtype.val) =
      (W.oldP.cycle.walk.edges.map (Sym2.map Subtype.val)).filter
        fun f => decide (f ≠ Sym2.map Subtype.val e) := by
    simpa only [Finset.mem_singleton, Finset.image_singleton] using
      map_filtered_complement (Sym2.map Subtype.val)
        (Sym2.map.injective Subtype.val_injective) W.oldP.cycle.walk.edges {e}
  have heraw := he.map (Sym2.map Subtype.val)
  rw [hefilter, hrawEdges] at heraw
  have heval : Sym2.map Subtype.val e =
      s(rightPort O (2 + j.val), leftPort O (2 + j.val)) := rfl
  rw [heval] at heraw
  have hwhole := actual_joint_split_cut_inventory W.P.seed.walk
    W.P.seed.hamiltonian.isCycle
    ((List.ofFn W.P.seed.joint).flatMap fun p => p.walk.edges)
    W.P.seed.K W.P.seed.H W.P.seed.partitions.disjoint
    W.P.seed.partitions.joint_partition.edges W.P.seed.partitions.joint_partition.cut_mem
  have hrawWhole := (hwhole.map (Sym2.map Subtype.val)).filter
    (fun f => decide (f ≠ s(rightPort O (2 + j.val), leftPort O (2 + j.val))))
  exact ⟨hsraw.trans hsJoint.symm, heraw, heraw.trans hrawWhole⟩

#print axioms native_j2_original_p_opening_inventory

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion
