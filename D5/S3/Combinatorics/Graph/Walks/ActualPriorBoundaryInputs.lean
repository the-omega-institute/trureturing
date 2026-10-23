/- GID: D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Verified actual partitions of one prior cycle recover the literal route prefixes and regrouped inventories for boundary updates. -/
import D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory
import D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualPriorBoundaryInputs

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory
open D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- The primary actual boundary is rooted at the distinguished old
joint path. Exact prior inventories earn both its literal initial
position and all regroupings used by the first-Q-cut restoration. -/
theorem actual_prior_primary_boundary_inputs {base ℓ z y : V}
    (w : G.Walk base base) (hw : w.IsCycle)
    (d : G.Walk ℓ z) (jointrest : List (Piece G))
    (old : G.Walk ℓ y) (oldrest : List (Piece G))
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hjointSupport : ((⟨ℓ, z, d⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.support).Perm w.support.tail)
    (hsingleSupport : ((⟨ℓ, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.support).Perm w.support.tail)
    (hjointEdges : ((⟨ℓ, z, d⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.edges).Perm (w.edges.filter fun e => decide (e ∉ K ∪ H)))
    (hsingleEdges : ((⟨ℓ, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.edges).Perm (w.edges.filter fun e => decide (e ∉ K)))
    (hcuts : ∀ e ∈ K ∪ H, e ∈ w.edges) :
    old.IsPath ∧ d.support.Nodup ∧ (∀ e ∈ d.edges, e ∈ old.edges) ∧
      (old.support ++ oldrest.flatMap fun p => p.walk.support).Nodup ∧
      (old.support ++ oldrest.flatMap fun p => p.walk.support).Perm
        (d.support ++ jointrest.flatMap fun p => p.walk.support) ∧
      (old.edges ++ oldrest.flatMap fun p => p.walk.edges).Perm
        (d.edges ++ (jointrest.flatMap fun p => p.walk.edges) ++ H.toList) ∧
      ∃ tail : G.Walk z y, old = d.append tail ∧ tail.IsPath := by
  classical
  have hnjoint : ((⟨ℓ, z, d⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.support).Nodup :=
    hjointSupport.nodup_iff.mpr hw.support_nodup
  obtain ⟨hnold, hs, he⟩ := actual_prior_single_order_partition_inventories w hw
    (⟨ℓ, z, d⟩ :: jointrest) (⟨ℓ, y, old⟩ :: oldrest) K H hdisjoint
    hjointSupport hsingleSupport hjointEdges hsingleEdges hcuts
  have hjointInventory (e : Sym2 V) :
      e ∈ ((⟨ℓ, z, d⟩ :: jointrest).flatMap fun p : Piece G => p.walk.edges) ↔
        e ∈ w.edges ∧ e ∉ K ∪ H := by
    rw [hjointEdges.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
  have hsingleInventory (e : Sym2 V) :
      e ∈ ((⟨ℓ, y, old⟩ :: oldrest).flatMap fun p : Piece G => p.walk.edges) ↔
        e ∈ w.edges ∧ e ∉ K := by
    rw [hsingleEdges.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
  obtain ⟨hnd, hkeep, tail, hfactor, htail⟩ :=
    actual_restored_initial_joint_prefix w d jointrest old oldrest hnjoint hnold
      K H hjointInventory hsingleInventory
  have holdPath : old.IsPath := SimpleGraph.Walk.IsPath.mk'
    (List.nodup_append'.mp hnold).1
  exact ⟨holdPath, hnd, hkeep, hnold, hs, he, tail, hfactor, htail⟩

/-- The opposite boundary starts at the end of an actual old crossing
piece. The restored old b seam joins its reverse to the distinguished
joint path. Both its simplicity and its retention in the actual boundary
are earned from the same prior source inventories. -/
theorem actual_prior_opposite_boundary_inputs {base ℓ z r x y : V}
    (w : G.Walk base base) (hw : w.IsCycle)
    (d : G.Walk ℓ z) (cross : G.Walk r x) (jointrest : List (Piece G))
    (old : G.Walk x y) (oldrest : List (Piece G))
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hjointSupport : ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.support).Perm w.support.tail)
    (hsingleSupport : ((⟨x, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.support).Perm w.support.tail)
    (hjointEdges : ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.edges).Perm (w.edges.filter fun e => decide (e ∉ K ∪ H)))
    (hsingleEdges : ((⟨x, y, old⟩ :: oldrest).flatMap
      fun p : Piece G => p.walk.edges).Perm (w.edges.filter fun e => decide (e ∉ K)))
    (hcuts : ∀ e ∈ K ∪ H, e ∈ w.edges) (hseam : s(r, ℓ) ∈ H) :
    ∃ hrestore : G.Adj r ℓ,
      let front := cross.reverse.concat hrestore
      old.IsPath ∧ (front.append d).support.Nodup ∧
      (∀ e ∈ (front.append d).edges, e ∈ old.edges) ∧
      (old.support ++ oldrest.flatMap fun p => p.walk.support).Nodup ∧
      (old.support ++ oldrest.flatMap fun p => p.walk.support).Perm
        (d.support ++ cross.support ++ jointrest.flatMap fun p => p.walk.support) ∧
      (old.edges ++ oldrest.flatMap fun p => p.walk.edges).Perm
        (d.edges ++ cross.edges ++ (jointrest.flatMap fun p => p.walk.edges) ++ H.toList) ∧
      ∃ tail : G.Walk z y, old = front.append (d.append tail) ∧ tail.IsPath := by
  classical
  have hnjoint : ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.support).Nodup :=
    hjointSupport.nodup_iff.mpr hw.support_nodup
  obtain ⟨hnold, hs, he⟩ := actual_prior_single_order_partition_inventories w hw
    (⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest) (⟨x, y, old⟩ :: oldrest) K H hdisjoint
    hjointSupport hsingleSupport hjointEdges hsingleEdges hcuts
  have hjointInventory (e : Sym2 V) :
      e ∈ ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest).flatMap fun p : Piece G => p.walk.edges) ↔
        e ∈ w.edges ∧ e ∉ K ∪ H := by
    rw [hjointEdges.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
  have hsingleInventory (e : Sym2 V) :
      e ∈ ((⟨x, y, old⟩ :: oldrest).flatMap fun p : Piece G => p.walk.edges) ↔
        e ∈ w.edges ∧ e ∉ K := by
    rw [hsingleEdges.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
  obtain ⟨hrestore, hnd, hkeep, tail, hfactor, htail⟩ :=
    actual_restored_bridge_route_prefix w d cross jointrest old oldrest hnjoint hnold
      K H hdisjoint hjointInventory hsingleInventory hcuts hseam
  have holdPath : old.IsPath := SimpleGraph.Walk.IsPath.mk'
    (List.nodup_append'.mp hnold).1
  refine ⟨hrestore, holdPath, hnd, hkeep, hnold, ?_, ?_, tail, hfactor, htail⟩
  · simpa only [List.flatMap_cons, List.append_assoc] using hs
  · simpa only [List.flatMap_cons, List.append_assoc] using he

#print axioms actual_prior_primary_boundary_inputs
#print axioms actual_prior_opposite_boundary_inputs

end D5.S3.Combinatorics.Graph.Walks.ActualPriorBoundaryInputs
