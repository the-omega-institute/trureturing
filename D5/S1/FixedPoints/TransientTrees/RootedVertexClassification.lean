/- GID: D5/S1/FixedPoints/TransientTrees/RootedVertexClassification
   generality: G
   mirror-B: D5/B/S1/FixedPoints/TransientTrees/RootedVertexClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual rooted vertex equivalences preserve branch codes and are classified by them. -/

import D5.S1.FixedPoints.TransientTrees.RootedVertexReconstruction

namespace D5.S1.FixedPoints.TransientTrees.RootedVertexClassification

open D5.S1.FixedPoints.RootedTransientTreeClassification
open D5.S1.FixedPoints.TransientTrees.RootedVertexReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

noncomputable section

private def childDescendant {Y : Type u} {f : Y -> Y} {r : Y}
    (a : Descendant f r) (c : {c : Y // TransientChild f c a.1}) : Descendant f r :=
  ⟨c.1, a.2.head c.2⟩

private def childFiberEquiv {Y : Type u} {Z : Type v}
    {f : Y -> Y} {g : Z -> Z} {r : Y} {s : Z}
    (e : RootedVertexEquiv f g r s) (a : Descendant f r) :
    {c : Y // TransientChild f c a.1} ≃
      {d : Z // TransientChild g d (e.equiv a).1} where
  toFun c := ⟨(e.equiv (childDescendant a c)).1,
    (e.child_iff (childDescendant a c) a).mp c.2⟩
  invFun d := ⟨(e.equiv.symm (childDescendant (e.equiv a) d)).1, by
    apply (e.child_iff (e.equiv.symm (childDescendant (e.equiv a) d)) a).mpr
    simpa only [Equiv.apply_symm_apply, childDescendant] using d.2⟩
  left_inv c := by
    apply Subtype.ext
    change (e.equiv.symm (e.equiv (childDescendant a c))).1 = c.1
    exact congrArg (fun x : Descendant f r => x.1)
      (e.equiv.symm_apply_apply (childDescendant a c))
  right_inv d := by
    apply Subtype.ext
    change (e.equiv (e.equiv.symm (childDescendant (e.equiv a) d))).1 = d.1
    exact congrArg (fun x : Descendant g s => x.1)
      (e.equiv.apply_symm_apply (childDescendant (e.equiv a) d))

-- Keep the given equivalence fixed while descending through all its original vertices.
private theorem descendant_branch_code_eq {Y : Type u} {Z : Type v}
    [Fintype Y] [Fintype Z] {f : Y -> Y} {g : Z -> Z} {r : Y} {s : Z}
    (e : RootedVertexEquiv f g r s) (a : Descendant f r) :
    branchCode f a.1 = branchCode g (e.equiv a).1 := by
  classical
  obtain ⟨a, ha⟩ := a
  induction a using (transient_child_well_founded f).induction with
  | h a ih =>
      let da : Descendant f r := ⟨a, ha⟩
      let ce := childFiberEquiv e da
      rw [branch_code_eq, branch_code_eq]
      apply congrArg Encodable.encode
      change Finset.univ.val.map (branchCode f ∘ Subtype.val) =
        Finset.univ.val.map (branchCode g ∘ Subtype.val)
      calc
        _ = Finset.univ.val.map ((branchCode g ∘ Subtype.val) ∘ ce) := by
          apply Multiset.map_congr rfl
          intro c _
          exact ih c.1 c.2 (ha.head c.2)
        _ = _ := by rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- An actual root-preserving vertex equivalence preserves the full branch code. -/
theorem branch_code_eq_of_rooted_vertex_equiv
    {Y : Type u} {Z : Type v} [Fintype Y] [Fintype Z]
    {f : Y -> Y} {g : Z -> Z} {r : Y} {s : Z}
    (e : RootedVertexEquiv f g r s) : branchCode f r = branchCode g s := by
  have invariant := descendant_branch_code_eq e ⟨r, .refl⟩
  simpa only [e.root_eq] using invariant

/-- Full branch codes classify the original rooted vertices and their internal child edges. -/
theorem rooted_vertex_classification
    {Y : Type u} {Z : Type v} [Fintype Y] [Fintype Z]
    {f : Y -> Y} {g : Z -> Z} {r : Y} {s : Z} :
    Nonempty (RootedVertexEquiv f g r s) ↔ branchCode f r = branchCode g s :=
  ⟨fun ⟨e⟩ => branch_code_eq_of_rooted_vertex_equiv e,
    rooted_vertex_equiv_of_branch_code_eq f g r s⟩

end

end D5.S1.FixedPoints.TransientTrees.RootedVertexClassification
