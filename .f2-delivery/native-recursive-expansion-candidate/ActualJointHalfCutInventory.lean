/- UNCOMPILED actual half-restoration cut inventory.
   Split two disjoint actual marked-cut groups of the same source cycle.
   The exact joint filtered inventory earns the source edge permutation;
   it is not assumed as a final regrouped parent inventory. -/
import D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

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
  have hseparate : H.toList.Perm ((H.erase seam).toList ++ [seam]) := by
    have hi : H.toList.Perm (seam :: (H.erase seam).toList) := by
      simpa only [Finset.insert_erase hseam] using
        (Finset.toList_insert (Finset.not_mem_erase seam H))
    exact hi.trans (by
      simpa only [List.singleton_append] using
        List.perm_append_comm [seam] (H.erase seam).toList)
  have hsource := hpartition.trans (hjoint.symm.append
    (hremoved.trans (hsplit.trans (hseparate.append (List.Perm.refl K.toList)))))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using hsource
  · intro hK
    exact Finset.disjoint_left.mp hdisjoint hK hseam
  · exact hdisjoint.symm.mono_left (Finset.erase_subset _ _)

#print axioms actual_joint_half_cut_inventory

end D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory
