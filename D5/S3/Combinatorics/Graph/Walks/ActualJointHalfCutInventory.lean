/- GID: D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same actual source cycle earns exact restored-cut inventories for single-order and half-boundary reconstruction. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open private filter_complement_of_nodup from
  D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

private theorem actual_joint_split_cut_inventory {base : V}
    (c : G.Walk base base) (hc : c.IsCycle) (jointEdges : List (Sym2 V))
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hjoint : jointEdges.Perm (c.edges.filter fun e => decide (e ∉ K ∪ H)))
    (hcuts : ∀ e ∈ K ∪ H, e ∈ c.edges) :
    c.edges.Perm (jointEdges ++ H.toList ++ K.toList) := by
  classical
  have hpartition : c.edges.Perm
      ((c.edges.filter fun e => decide (e ∉ K ∪ H)) ++
        (c.edges.filter fun e => decide (e ∈ K ∪ H))) := by
    apply List.perm_iff_count.mpr
    intro e
    simpa only [not_not, List.count_append] using
      List.count_eq_count_filter_add (fun e => e ∉ K ∪ H) c.edges e
  have hremoved : (c.edges.filter fun e => decide (e ∈ K ∪ H)).Perm (K ∪ H).toList := by
    apply (List.perm_ext_iff_of_nodup (hc.isTrail.edges_nodup.filter _)
      (Finset.nodup_toList _)).mpr
    intro e
    simp only [List.mem_filter, decide_eq_true_eq, Finset.mem_toList]
    exact ⟨fun h => h.2, fun h => ⟨hcuts e h, h⟩⟩
  have hsplit : (K ∪ H).toList.Perm (H.toList ++ K.toList) := by
    have hn : (H.toList ++ K.toList).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
      apply List.disjoint_left.mpr
      intro e heH heK
      exact Finset.disjoint_left.mp hdisjoint
        (Finset.mem_toList.mp heK) (Finset.mem_toList.mp heH)
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hn).mpr
    intro e
    simp only [Finset.mem_toList, List.mem_append, Finset.mem_union]
    exact or_comm
  simpa only [List.append_assoc] using
    hpartition.trans (hjoint.symm.append (hremoved.trans hsplit))

/-- Both inventories concern the same actual cycle. Restoring H from the
joint partition earns the exact old single-order inventory, rather than
assuming a pre-regrouped restoration certificate. -/
theorem actual_restored_single_order_inventory {base : V}
    (c : G.Walk base base) (hc : c.IsCycle)
    (jointEdges singleEdges : List (Sym2 V))
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hjoint : jointEdges.Perm (c.edges.filter fun e => decide (e ∉ K ∪ H)))
    (hsingle : singleEdges.Perm (c.edges.filter fun e => decide (e ∉ K)))
    (hcuts : ∀ e ∈ K ∪ H, e ∈ c.edges) :
    singleEdges.Perm (jointEdges ++ H.toList) := by
  classical
  have hsource := actual_joint_split_cut_inventory c hc jointEdges K H
    hdisjoint hjoint hcuts
  have hsource' : c.edges.Perm ((jointEdges ++ H.toList) ++ K.toList) := by
    simpa only [List.append_assoc] using hsource
  have hn : ((jointEdges ++ H.toList) ++ K.toList).Nodup :=
    hsource'.nodup_iff.mp hc.isTrail.edges_nodup
  have hfiltered := List.Perm.filter (fun e => decide (e ∉ K)) hsource'
  have hfilter : ((jointEdges ++ H.toList) ++ K.toList).filter
      (fun e => decide (e ∉ K)) = jointEdges ++ H.toList := by
    simpa only [Finset.toList_toFinset] using
      filter_complement_of_nodup (jointEdges ++ H.toList) K.toList hn
  rw [hfilter] at hfiltered
  exact hsingle.trans hfiltered

/-- The prior actual single-order and joint states both partition the
same old cycle. Their verified inventories earn every old support and
edge regrouping needed by the next boundary update. The single-order
support is simple because it is a permutation of the actual cycle's
nonrepeating tail, including after inclusion in a larger graph. -/
theorem actual_prior_single_order_partition_inventories {base : V}
    (c : G.Walk base base) (hc : c.IsCycle)
    (joint single : List (Piece G))
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hjointSupport : (joint.flatMap fun p => p.walk.support).Perm c.support.tail)
    (hsingleSupport : (single.flatMap fun p => p.walk.support).Perm c.support.tail)
    (hjointEdges : (joint.flatMap fun p => p.walk.edges).Perm
      (c.edges.filter fun e => decide (e ∉ K ∪ H)))
    (hsingleEdges : (single.flatMap fun p => p.walk.edges).Perm
      (c.edges.filter fun e => decide (e ∉ K)))
    (hcuts : ∀ e ∈ K ∪ H, e ∈ c.edges) :
    (single.flatMap fun p => p.walk.support).Nodup ∧
    (single.flatMap fun p => p.walk.support).Perm
      (joint.flatMap fun p => p.walk.support) ∧
    (single.flatMap fun p => p.walk.edges).Perm
      ((joint.flatMap fun p => p.walk.edges) ++ H.toList) := by
  have hn : (single.flatMap fun p => p.walk.support).Nodup :=
    hsingleSupport.nodup_iff.mpr hc.support_nodup
  exact ⟨hn, hsingleSupport.trans hjointSupport.symm,
    actual_restored_single_order_inventory c hc _ _ K H hdisjoint
      hjointEdges hsingleEdges hcuts⟩

/-- Restore precisely H and continue deleting precisely K. The chosen
new opposite-order cut is isolated from H; all other restored cuts come
from H.erase seam. Cycle simplicity and exact joint inventory supply the
complete source edge permutation used by actual boundary restoration. -/
theorem actual_joint_half_cut_inventory {base : V}
    (c : G.Walk base base) (hc : c.IsCycle) (jointEdges : List (Sym2 V))
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hjoint : jointEdges.Perm (c.edges.filter fun e => decide (e ∉ K ∪ H)))
    (hcuts : ∀ e ∈ K ∪ H, e ∈ c.edges)
    (seam : Sym2 V) (hseam : seam ∈ H) :
    c.edges.Perm (jointEdges ++ (H.erase seam).toList ++ [seam] ++ K.toList) ∧
      seam ∉ K ∧ Disjoint (H.erase seam) K := by
  classical
  have hseparate : H.toList.Perm ((H.erase seam).toList ++ [seam]) := by
    have hi : H.toList.Perm (seam :: (H.erase seam).toList) := by
      simpa only [Finset.insert_erase hseam] using
        (Finset.toList_insert (by simp : seam ∉ H.erase seam))
    have hswap : ([seam] ++ (H.erase seam).toList).Perm
        ((H.erase seam).toList ++ [seam]) := List.perm_append_comm
    exact hi.trans (by simpa only [List.singleton_append] using hswap)
  have hstep : (jointEdges ++ H.toList ++ K.toList).Perm
      (jointEdges ++ (H.erase seam).toList ++ [seam] ++ K.toList) := by
    simpa only [List.append_assoc] using
      ((List.Perm.refl jointEdges).append (hseparate.append (List.Perm.refl K.toList)))
  have hsource := (actual_joint_split_cut_inventory c hc jointEdges K H
    hdisjoint hjoint hcuts).trans hstep
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using hsource
  · intro hK
    exact Finset.disjoint_left.mp hdisjoint hK hseam
  · exact hdisjoint.symm.mono_left (Finset.erase_subset _ _)

#print axioms actual_joint_half_cut_inventory
#print axioms actual_restored_single_order_inventory
#print axioms actual_prior_single_order_partition_inventories

end D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory
