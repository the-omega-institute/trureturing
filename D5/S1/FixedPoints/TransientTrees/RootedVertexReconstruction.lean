/- GID: D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction
   generality: G
   mirror-B: D5/B/S1/FixedPoints/TransientTrees/RootedVertexReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal branch codes reconstruct actual rooted vertices and internal child edges. -/

import D5.S1.FixedPoints.RootedTransientTreeClassification
import Mathlib.Logic.Equiv.Option

namespace D5.S1.FixedPoints.TransientTrees.RootedVertexReconstruction

open D5.S1.FixedPoints.RootedTransientTreeClassification
open Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

noncomputable section

/-- Original vertices whose transient-child path ends at the specified root. -/
abbrev Descendant {Y : Type u} (update : Y → Y) (root : Y) :=
  {x : Y // ReflTransGen (TransientChild update) x root}

/-- A bijection of original descendant vertices, including the root and both edge directions. -/
structure RootedVertexEquiv {Y : Type u} {Z : Type v}
    (updateY : Y → Y) (updateZ : Z → Z) (rootY : Y) (rootZ : Z) where
  equiv : Descendant updateY rootY ≃ Descendant updateZ rootZ
  root_eq : equiv ⟨rootY, .refl⟩ = ⟨rootZ, .refl⟩
  child_iff : ∀ a b : Descendant updateY rootY,
    TransientChild updateY a.1 b.1 ↔
      TransientChild updateZ (equiv a).1 (equiv b).1

private theorem parent_unique {Y : Type u} (f : Y → Y) :
    Relator.RightUnique (TransientChild f) :=
  fun _ _ _ ha hb => ha.2.symm.trans hb.2

private theorem no_return {Y : Type u} [Finite Y] {f : Y → Y} {a b : Y}
    (edge : TransientChild f a b) (path : ReflTransGen (TransientChild f) b a) : False :=
  (transient_child_well_founded f).transGen.irrefl.irrefl a (TransGen.head' edge path)

private theorem child_path_eq {Y : Type u} [Finite Y] {f : Y → Y} {r a b : Y}
    (ha : TransientChild f a r) (hb : TransientChild f b r)
    (path : ReflTransGen (TransientChild f) a b) : a = b := by
  rcases path.cases_head with same | ⟨p, hp, rest⟩
  · exact same
  · have same := parent_unique f ha hp
    subst p
    exact (no_return hb rest).elim

private theorem child_unique {Y : Type u} [Finite Y] {f : Y → Y} {r x a b : Y}
    (ha : TransientChild f a r) (hb : TransientChild f b r)
    (xa : ReflTransGen (TransientChild f) x a)
    (xb : ReflTransGen (TransientChild f) x b) : a = b := by
  rcases xa.total_of_right_unique (parent_unique f) xb with ab | ba
  · exact child_path_eq ha hb ab
  · exact (child_path_eq hb ha ba).symm

private abbrev Pieces {Y : Type u} (f : Y → Y) (r : Y) :=
  Option (Σ c : {c : Y // TransientChild f c r}, Descendant f c.1)

private def assemble {Y : Type u} (f : Y → Y) (r : Y) : Pieces f r → Descendant f r
  | none => ⟨r, .refl⟩
  | some ⟨c, x⟩ => ⟨x.1, x.2.tail c.2⟩

private theorem assemble_bijective {Y : Type u} [Finite Y] (f : Y → Y) (r : Y) :
    Function.Bijective (assemble f r) := by
  constructor
  · intro a b eqv
    have h := congrArg Subtype.val eqv
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            change r = b.2.1 at h
            have path := b.2.2
            rw [← h] at path
            exact (no_return b.1.2 path).elim
    | some a =>
        cases b with
        | none =>
            change a.2.1 = r at h
            have path := a.2.2
            rw [h] at path
            exact (no_return a.1.2 path).elim
        | some b =>
            obtain ⟨c, x⟩ := a
            obtain ⟨d, y⟩ := b
            have cd : c = d := Subtype.ext (child_unique c.2 d.2 x.2 (h ▸ y.2))
            subst d
            have xy : x = y := Subtype.ext h
            subst y
            rfl
  · rintro ⟨x, hx⟩
    rcases hx.cases_tail with hr | ⟨c, hc, edge⟩
    · subst x
      exact ⟨none, rfl⟩
    · exact ⟨some ⟨⟨c, edge⟩, ⟨x, hc⟩⟩, rfl⟩

/-- The actual root-plus-child-subtree partition; its inverse locates every original vertex. -/
def descendantPartition {Y : Type u} [Finite Y] (f : Y → Y) (r : Y) :
    Option (Σ c : {c : Y // TransientChild f c r}, Descendant f c.1) ≃
      Descendant f r :=
  Equiv.ofBijective (assemble f r) (assemble_bijective f r)

private theorem root_no_edge {Y : Type u} [Finite Y] {f : Y → Y} {r : Y}
    (x : Descendant f r) : ¬ TransientChild f r x.1 :=
  fun edge => no_return edge x.2

private theorem piece_edge_root {Y : Type u} [Finite Y] {f : Y → Y} {r : Y}
    (c : {c : Y // TransientChild f c r}) (x : Descendant f c.1) :
    TransientChild f x.1 r ↔ x = ⟨c.1, .refl⟩ := by
  constructor
  · intro edge
    exact Subtype.ext (child_unique edge c.2 .refl x.2)
  · rintro rfl
    exact c.2

private theorem piece_edge_piece {Y : Type u} [Finite Y] {f : Y → Y} {r : Y}
    (c d : {c : Y // TransientChild f c r})
    (x : Descendant f c.1) (y : Descendant f d.1) :
    TransientChild f x.1 y.1 ↔ c = d ∧ TransientChild f x.1 y.1 := by
  constructor
  · intro edge
    exact ⟨Subtype.ext (child_unique c.2 d.2 x.2 (y.2.head edge)), edge⟩
  · exact And.right

open Classical in
private def childOccurrences {Y : Type u} [Fintype Y] (f : Y → Y) (r : Y) :
    {c : Y // TransientChild f c r} ≃ (transientChildren f r).ToType := by
  classical
  refine ⟨fun c => ⟨c, ⟨0, by simp [transientChildren]⟩⟩, Sigma.fst,
    fun _ => rfl, ?_⟩
  rintro ⟨c, i⟩
  have hi : i.val = 0 := by
    have bound := i.2
    simp only [transientChildren, Multiset.count_univ] at bound
    omega
  have eqi : i = ⟨0, by simp [transientChildren]⟩ := Fin.ext hi
  cases eqi
  rfl

private theorem matching_children {Y : Type u} {Z : Type v} [Fintype Y] [Fintype Z]
    {f : Y → Y} {g : Z → Z} {r : Y} {s : Z}
    (codes : branchCode f r = branchCode g s) :
    ∃ e : {c : Y // TransientChild f c r} ≃ {d : Z // TransientChild g d s},
      ∀ c, branchCode f c.1 = branchCode g (e c).1 := by
  classical
  have hm : (transientChildren f r).map (branchCode f ∘ Subtype.val) =
      (transientChildren g s).map (branchCode g ∘ Subtype.val) := by
    simpa only [branch_code_eq, Encodable.encode_inj] using codes
  let left := (childOccurrences f r).trans
    ((transientChildren f r).mapEquiv (branchCode f ∘ Subtype.val))
  let right := (childOccurrences g s).trans
    ((transientChildren g s).mapEquiv (branchCode g ∘ Subtype.val))
  let e := (left.trans (Multiset.cast hm)).trans right.symm
  refine ⟨e, fun c => ?_⟩
  have h : right (e c) = Multiset.cast hm (left c) := by
    exact right.apply_symm_apply _
  have hv := congrArg Sigma.fst h
  change (right (e c)).fst = (left c).fst at hv
  simp only [right, left, Equiv.trans_apply, Multiset.mapEquiv_apply,
    Function.comp_apply] at hv
  exact hv.symm

private def glue_children {Y : Type u} {Z : Type v} [Finite Y] [Finite Z]
    {f : Y → Y} {g : Z → Z} {r : Y} {s : Z}
    (ce : {c : Y // TransientChild f c r} ≃ {d : Z // TransientChild g d s})
    (sub : ∀ c, RootedVertexEquiv f g c.1 (ce c).1) : RootedVertexEquiv f g r s := by
  let pe : Pieces f r ≃ Pieces g s :=
    (Equiv.sigmaCongr ce (fun c => (sub c).equiv)).optionCongr
  have edges : ∀ a b : Pieces f r,
      TransientChild f (assemble f r a).1 (assemble f r b).1 ↔
        TransientChild g (assemble g s (pe a)).1 (assemble g s (pe b)).1 := by
    intro a b
    cases a with
    | none =>
        exact iff_of_false (root_no_edge (assemble f r b))
          (root_no_edge (assemble g s (pe b)))
    | some a =>
        obtain ⟨c, x⟩ := a
        cases b with
        | none =>
            change TransientChild f x.1 r ↔ TransientChild g ((sub c).equiv x).1 s
            rw [piece_edge_root c x, piece_edge_root (ce c) ((sub c).equiv x),
              ← (sub c).root_eq]
            exact (sub c).equiv.injective.eq_iff.symm
        | some b =>
            obtain ⟨d, y⟩ := b
            change TransientChild f x.1 y.1 ↔
              TransientChild g ((sub c).equiv x).1 ((sub d).equiv y).1
            classical
            by_cases cd : c = d
            · subst d
              exact (sub c).child_iff x y
            · rw [piece_edge_piece c d x y,
                piece_edge_piece (ce c) (ce d) ((sub c).equiv x) ((sub d).equiv y)]
              simp only [cd, ce.injective.eq_iff, false_and]
  let e := (descendantPartition f r).symm.trans (pe.trans (descendantPartition g s))
  refine ⟨e, ?_, ?_⟩
  · change e (descendantPartition f r none) = descendantPartition g s none
    simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  · intro x y
    obtain ⟨a, rfl⟩ := (descendantPartition f r).surjective x
    obtain ⟨b, rfl⟩ := (descendantPartition f r).surjective y
    simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
    simpa only [descendantPartition, Equiv.ofBijective_apply] using edges a b

/-- Equal full branch codes yield an actual rooted equivalence, even for unequal ambient sizes. -/
theorem rooted_vertex_equiv_of_branch_code_eq
    {Y : Type u} {Z : Type v} [Fintype Y] [Fintype Z]
    (f : Y → Y) (g : Z → Z) (r : Y) (s : Z)
    (codes : branchCode f r = branchCode g s) : Nonempty (RootedVertexEquiv f g r s) := by
  classical
  induction r using (transient_child_well_founded f).induction generalizing s with
  | h r ih =>
      obtain ⟨ce, hc⟩ := matching_children codes
      exact ⟨glue_children ce (fun c => Classical.choice (ih c.1 c.2 (ce c).1 (hc c)))⟩

/-- The frozen recursive matching predicate also reconstructs the original vertices. -/
theorem rooted_vertex_equiv_of_recursive_isomorphism
    {Y : Type u} {Z : Type v} [Fintype Y] [Fintype Z]
    (f : Y → Y) (g : Z → Z) (r : Y) (s : Z)
    (matching : RootedTransientTreeIsomorphic f g r s) :
    Nonempty (RootedVertexEquiv f g r s) :=
  rooted_vertex_equiv_of_branch_code_eq f g r s
    ((rooted_transient_tree_classification f g r s).mp matching)

end

end D5.S1.FixedPoints.TransientTrees.RootedVertexReconstruction
