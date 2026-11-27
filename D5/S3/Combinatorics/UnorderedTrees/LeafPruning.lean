/- GID: D5/S3/Combinatorics/UnorderedTrees/LeafPruning
   generality: G
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/LeafPruning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Leaf pruning preserves the rooted parent tree and lowers vertex-height by one. -/

import D5.S3.Combinatorics.UnorderedTrees.ParentTree

/-! Leaf pruning retains the actual internal-vertex subtree. -/

namespace D5.S3.Combinatorics.UnorderedTrees.LeafPruning

open D5.S3.Combinatorics.UnorderedTrees.ParentTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

attribute [local instance] Classical.propDecidable

private def prunedParent {V : Type u} (T : Tree V) (hr : Internal T T.root)
    (v : {v // Internal T v}) : {v // Internal T v} :=
  ⟨T.parent v.1, by
    by_cases hv : v.1 = T.root
    · simpa only [hv, T.fixed_root] using hr
    · exact ⟨v.1, hv, rfl⟩⟩

private theorem iterate_prunedParent {V : Type u} (T : Tree V) (hr : Internal T T.root)
    (k : ℕ) (v : {v // Internal T v}) :
    ((prunedParent T hr)^[k] v).1 = (T.parent^[k]) v.1 :=
by
  have h : Function.Semiconj
      (fun v : {v // Internal T v} => v.1) (prunedParent T hr) T.parent := fun _ => rfl
  exact h.iterate_right k v

/-- Delete precisely the original leaves, retaining all original internal vertices and edges. -/
def prune {V : Type u} (T : Tree V) (hr : Internal T T.root) :
    Tree {v // Internal T v} where
  parent := prunedParent T hr
  root := ⟨T.root, hr⟩
  fixed_root := Subtype.ext T.fixed_root
  reaches v := by
    obtain ⟨k, hk⟩ := T.reaches v.1
    exact ⟨k, Subtype.ext ((iterate_prunedParent T hr k v).trans hk)⟩

private theorem depth_prune {V : Type u} (T : Tree V) (hr : Internal T T.root)
    (v : {v // Internal T v}) : depth (prune T hr) v = depth T v.1 := by
  apply Nat.le_antisymm
  · apply depth_le (prune T hr)
    apply Subtype.ext
    exact (iterate_prunedParent T hr _ v).trans (reaches_depth T v.1)
  · apply depth_le T
    have h := congrArg Subtype.val (reaches_depth (prune T hr) v)
    exact (iterate_prunedParent T hr _ v).symm.trans h

private theorem pruning_height {V : Type u} [Fintype V] (T : Tree V)
    (hr : Internal T T.root) : height T = height (prune T hr) + 1 := by
  let D := Finset.univ.sup (depth T)
  let K := Finset.univ.sup (fun v : {v // Internal T v} => depth T v.1)
  have hD (v : V) : depth T v ≤ D := Finset.le_sup (Finset.mem_univ v)
  have hK (v : {v // Internal T v}) : depth T v.1 ≤ K :=
    Finset.le_sup (f := fun x : {v // Internal T v} => depth T x.1)
      (Finset.mem_univ v)
  have upper : D ≤ K + 1 := by
    apply Finset.sup_le
    intro v _
    by_cases hv : v = T.root
    · simpa only [hv, depth_root] using (Nat.zero_le (K + 1))
    · have h := hK ⟨T.parent v, ⟨v, hv, rfl⟩⟩
      change depth T (T.parent v) ≤ K at h
      rw [depth_parent T hv]
      omega
  have lower : K ≤ D - 1 := by
    apply Finset.sup_le
    intro v _
    obtain ⟨w, hw⟩ := v.2
    have h := hD w
    rw [depth_parent T hw.1, hw.2] at h
    omega
  have positive : 1 ≤ D := by
    obtain ⟨w, hw⟩ := hr
    have h := hD w
    rw [depth_parent T hw.1, hw.2, depth_root] at h
    exact h
  have eqmax : D = K + 1 := by omega
  have hheight : height (prune T hr) = K + 1 := by
    unfold height
    congr 1
    apply Finset.sup_congr rfl
    intro v _
    exact depth_prune T hr v
  change D + 1 = height (prune T hr) + 1
  rw [hheight, eqmax]

private theorem root_internal_of_nonroot {V : Type u} (T : Tree V) {v : V}
    (hv : v ≠ T.root) : Internal T T.root := by
  have hpos : 0 < depth T v := by
    by_contra h
    have hz : depth T v = 0 := by omega
    have h := reaches_depth T v
    simp only [hz, Function.iterate_zero, id_eq] at h
    exact hv h
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  refine ⟨(T.parent^[k]) v, ?_, ?_⟩
  · intro h
    have hle := depth_le T h
    omega
  · have h := reaches_depth T v
    simpa only [hk, Function.iterate_succ_apply'] using h

/-- Every tree satisfying the target equality has a nonempty internal rooted subtree. -/
theorem qualifying_root {V : Type u} [Fintype V] (T : Tree V)
    (h : height T = internalCount T) : Internal T T.root := by
  have hp : 0 < internalCount T := by
    rw [← h]
    exact Nat.succ_pos _
  obtain ⟨⟨v, hv⟩⟩ := (Fintype.card_pos_iff).mp hp
  obtain ⟨w, hw⟩ := hv
  exact root_internal_of_nonroot T hw.1

/-- The actual leaf-pruning reduction, with vertex-height rather than edge-height. -/
theorem pruning_reduction {V : Type u} [Fintype V] (T : Tree V)
    (hr : Internal T T.root) :
    height T = height (prune T hr) + 1 ∧
      (height T = internalCount T ↔
        Fintype.card {v // Internal T v} = height (prune T hr) + 1) := by
  have h := pruning_height T hr
  exact ⟨h, by rw [h]; exact eq_comm⟩

#print axioms qualifying_root
#print axioms pruning_reduction

end

end D5.S3.Combinatorics.UnorderedTrees.LeafPruning
