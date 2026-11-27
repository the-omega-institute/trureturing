/- GID: D5/S3/Combinatorics/UnorderedTrees/ParentTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/ParentTree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite rooted parent trees, their actual vertex isomorphisms and leaf pruning. -/

import D5.S1.FixedPoints.TransientTrees.RootedVertexClassification
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import OmegaBuild.Commands

compile_only_with_mathlib

/-! Rooted parent data retain their actual vertices and all nonroot parent edges. -/

namespace D5.S3.Combinatorics.UnorderedTrees.ParentTree

open D5.S1.FixedPoints.RootedTransientTreeClassification
open D5.S1.FixedPoints.TransientTrees.RootedVertexReconstruction
open D5.S1.FixedPoints.TransientTrees.RootedVertexClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A rooted tree on its actual vertices: the root is fixed, and every vertex reaches it. -/
structure Tree (V : Type u) where
  parent : V → V
  root : V
  fixed_root : parent root = root
  reaches : ∀ v, ∃ k : ℕ, (parent^[k]) v = root

/-- Actual rooted vertex isomorphisms; there is no order on the children. -/
structure Iso {V : Type u} {W : Type v} (T : Tree V) (S : Tree W) where
  equiv : V ≃ W
  root_eq : equiv T.root = S.root
  parent_eq : ∀ v, equiv (T.parent v) = S.parent (equiv v)

def Iso.symm {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : Iso T S) : Iso S T where
  equiv := e.equiv.symm
  root_eq := e.equiv.symm_apply_eq.mpr e.root_eq.symm
  parent_eq w := e.equiv.injective (by simp [e.parent_eq])

def Iso.trans {V : Type u} {W : Type v} {Z : Type*} {T : Tree V} {S : Tree W}
    {R : Tree Z} (e : Iso T S) (f : Iso S R) : Iso T R where
  equiv := e.equiv.trans f.equiv
  root_eq := by simp [e.root_eq, f.root_eq]
  parent_eq v := by simp [e.parent_eq, f.parent_eq]

/-- Transport a parent map along a change of vertex labels. -/
def relabel {V : Type u} {W : Type v} (T : Tree V) (e : V ≃ W) : Tree W where
  parent w := e (T.parent (e.symm w))
  root := e T.root
  fixed_root := by simp [T.fixed_root]
  reaches w := by
    have hc : Function.Semiconj e T.parent (fun w => e (T.parent (e.symm w))) :=
      fun v => by simp
    obtain ⟨k, hk⟩ := T.reaches (e.symm w)
    refine ⟨k, ?_⟩
    simpa only [Equiv.apply_symm_apply, hk] using (hc.iterate_right k (e.symm w)).symm

def relabelIso {V : Type u} {W : Type v} (T : Tree V) (e : V ≃ W) : Iso T (relabel T e) :=
  ⟨e, rfl, fun v => by simp [relabel]⟩

/-- A child edge omits the artificial fixed loop at the root. -/
def Child {V : Type u} (T : Tree V) (v w : V) : Prop :=
  v ≠ T.root ∧ T.parent v = w

/-- An internal vertex has at least one actual child. -/
def Internal {V : Type u} (T : Tree V) (v : V) : Prop := ∃ w, Child T w v

/-- Depth counts edges from a vertex to the root. -/
def depth {V : Type u} (T : Tree V) (v : V) : ℕ := Nat.find (T.reaches v)

theorem reaches_depth {V : Type u} (T : Tree V) (v : V) :
    (T.parent^[depth T v]) v = T.root := Nat.find_spec (T.reaches v)

theorem depth_le {V : Type u} (T : Tree V) {v : V} {k : ℕ}
    (h : (T.parent^[k]) v = T.root) : depth T v ≤ k := Nat.find_min' _ h

theorem depth_root {V : Type u} (T : Tree V) : depth T T.root = 0 :=
  Nat.eq_zero_of_le_zero (depth_le T (k := 0) rfl)

private theorem depth_eq_zero {V : Type u} (T : Tree V) (v : V) :
    depth T v = 0 ↔ v = T.root := by
  constructor
  · intro h
    simpa only [h, Function.iterate_zero, id_eq] using reaches_depth T v
  · rintro rfl
    exact depth_root T

theorem depth_parent {V : Type u} (T : Tree V) {v : V} (hv : v ≠ T.root) :
    depth T v = depth T (T.parent v) + 1 := by
  have hpos : 0 < depth T v := Nat.pos_of_ne_zero (mt (depth_eq_zero T v).mp hv)
  have hu : depth T v ≤ depth T (T.parent v) + 1 := by
    apply depth_le T
    simpa only [Function.iterate_succ_apply] using reaches_depth T (T.parent v)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hl : depth T (T.parent v) ≤ k := by
    apply depth_le T
    have h := reaches_depth T v
    simpa only [hk, Function.iterate_succ_apply] using h
  omega

private theorem periodic_iff_root {V : Type u} (T : Tree V) (v : V) :
    v ∈ Function.periodicPts T.parent ↔ v = T.root := by
  constructor
  · rintro ⟨p, hp, hperiod⟩
    obtain ⟨k, hk⟩ := T.reaches v
    induction k generalizing v with
    | zero => simpa using hk
    | succ k ih =>
        have hparent : T.parent v = T.root :=
          ih (T.parent v) hperiod.apply (by
            simpa only [Function.iterate_succ_apply] using hk)
        exact hperiod.eq_of_apply_eq_same
          ((show Function.IsFixedPt T.parent T.root from T.fixed_root).isPeriodicPt p)
          hp (hparent.trans T.fixed_root.symm)
  · rintro rfl
    exact Function.mk_mem_periodicPts (by decide : 0 < 1)
      ((show Function.IsFixedPt T.parent T.root from T.fixed_root).isPeriodicPt 1)

private theorem transient_iff_child {V : Type u} (T : Tree V) (v w : V) :
    TransientChild T.parent v w ↔ Child T v w := by
  simp only [TransientChild, Child, periodic_iff_root]

private theorem all_descendant {V : Type u} (T : Tree V) (v : V) :
    Relation.ReflTransGen (TransientChild T.parent) v T.root := by
  obtain ⟨k, hk⟩ := T.reaches v
  induction k generalizing v with
  | zero =>
      have h : v = T.root := by simpa using hk
      subst v
      exact .refl
  | succ k ih =>
      by_cases hv : v = T.root
      · subst v
        exact .refl
      · exact (ih (T.parent v) (by
          simpa only [Function.iterate_succ_apply] using hk)).head
          ((transient_iff_child T v (T.parent v)).mpr ⟨hv, rfl⟩)

private def descendantEquiv {V : Type u} (T : Tree V) : V ≃ Descendant T.parent T.root where
  toFun v := ⟨v, all_descendant T v⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

private def ofRootedVertexEquiv {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : RootedVertexEquiv T.parent S.parent T.root S.root) : Iso T S where
  equiv := (descendantEquiv T).trans (e.equiv.trans (descendantEquiv S).symm)
  root_eq := congrArg Subtype.val e.root_eq
  parent_eq v := by
    by_cases hv : v = T.root
    · subst v
      rw [T.fixed_root]
      change (e.equiv ⟨T.root, .refl⟩).1 = S.parent (e.equiv ⟨T.root, .refl⟩).1
      rw [e.root_eq]
      exact S.fixed_root.symm
    · exact ((e.child_iff (descendantEquiv T v) (descendantEquiv T (T.parent v))).mp
        ((transient_iff_child T v (T.parent v)).mpr ⟨hv, rfl⟩)).2.symm

private theorem iso_iterate {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : Iso T S) (k : ℕ) (v : V) :
    e.equiv ((T.parent^[k]) v) = (S.parent^[k]) (e.equiv v) :=
  (show Function.Semiconj e.equiv T.parent S.parent from e.parent_eq).iterate_right k v

theorem iso_child {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : Iso T S) (a b : V) : Child T a b ↔ Child S (e.equiv a) (e.equiv b) := by
  unfold Child
  constructor
  · rintro ⟨ha, hp⟩
    constructor
    · intro h
      exact ha (e.equiv.injective (h.trans e.root_eq.symm))
    · rw [← e.parent_eq, hp]
  · rintro ⟨ha, hp⟩
    constructor
    · intro h
      apply ha
      rw [h, e.root_eq]
    · apply e.equiv.injective
      rw [e.parent_eq, hp]

private def toRootedVertexEquiv {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : Iso T S) : RootedVertexEquiv T.parent S.parent T.root S.root where
  equiv := (descendantEquiv T).symm.trans (e.equiv.trans (descendantEquiv S))
  root_eq := Subtype.ext e.root_eq
  child_iff a b := by
    exact (transient_iff_child T a.1 b.1).trans
      ((iso_child e a.1 b.1).trans (transient_iff_child S _ _).symm)

/-- Branch-code equality is precisely isomorphism of all original vertices and parent edges. -/
theorem code_eq_iff_iso {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (T : Tree V) (S : Tree W) :
    branchCode T.parent T.root = branchCode S.parent S.root ↔ Nonempty (Iso T S) := by
  constructor
  · intro h
    obtain ⟨e⟩ := (rooted_vertex_classification).mpr h
    exact ⟨ofRootedVertexEquiv e⟩
  · rintro ⟨e⟩
    exact branch_code_eq_of_rooted_vertex_equiv (toRootedVertexEquiv e)

theorem iso_depth {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : Iso T S) (v : V) : depth S (e.equiv v) = depth T v := by
  apply Nat.le_antisymm
  · apply depth_le S
    rw [← iso_iterate e, reaches_depth, e.root_eq]
  · apply depth_le T
    apply e.equiv.injective
    rw [iso_iterate, reaches_depth, e.root_eq]

theorem iso_internal {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : Iso T S) (v : V) : Internal T v ↔ Internal S (e.equiv v) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨e.equiv w, (iso_child e w v).mp hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨e.equiv.symm w, (iso_child e _ v).mpr (by simpa using hw)⟩

def internalEquiv {V : Type u} {W : Type v} {T : Tree V} {S : Tree W}
    (e : Iso T S) : {v // Internal T v} ≃ {w // Internal S w} :=
  e.equiv.subtypeEquiv (iso_internal e)

/-- Vertex-height is one plus the maximum edge-depth, including the root. -/
def height {V : Type u} [Fintype V] (T : Tree V) : ℕ :=
  Finset.univ.sup (depth T) + 1

/-- The number of internal original vertices. -/
def internalCount {V : Type u} [Fintype V] (T : Tree V) : ℕ :=
  Fintype.card {v // Internal T v}

theorem iso_height {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {T : Tree V} {S : Tree W} (e : Iso T S) : height T = height S := by
  unfold height
  congr 1
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro v _
    rw [← iso_depth e v]
    exact Finset.le_sup (Finset.mem_univ (e.equiv v))
  · apply Finset.sup_le
    intro w _
    have h := iso_depth e (e.equiv.symm w)
    simp only [Equiv.apply_symm_apply] at h
    rw [h]
    exact Finset.le_sup (Finset.mem_univ (e.equiv.symm w))

/-- Finite parent data on `Fin n`, modulo actual unordered rooted-tree isomorphism. -/
def treeSetoid (n : ℕ) : Setoid (Tree (Fin n)) :=
  { r := fun T S => branchCode T.parent T.root = branchCode S.parent S.root
    iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩ }

/-- The actual unordered isomorphism-class carrier of size `n`. -/
abbrev TreeClass (n : ℕ) := Quotient (treeSetoid n)

private instance finite_tree (n : ℕ) : Finite (Tree (Fin n)) := by
  apply Finite.of_injective (fun T : Tree (Fin n) => (T.parent, T.root))
  intro T S h
  cases T
  cases S
  cases h
  rfl

instance fintype_tree (n : ℕ) : Fintype (Tree (Fin n)) := Fintype.ofFinite _
instance fintype_classes (n : ℕ) : Fintype (TreeClass n) := by
  classical
  exact Quotient.fintype _

/-- Vertex-height on actual unordered isomorphism classes. -/
def classHeight {n : ℕ} : TreeClass n → ℕ :=
  Quotient.lift height (by
    intro T S h
    obtain ⟨e⟩ := (code_eq_iff_iso T S).mp h
    exact iso_height e)

/-- Internal-vertex count on actual unordered isomorphism classes. -/
def classInternalCount {n : ℕ} : TreeClass n → ℕ :=
  Quotient.lift internalCount (by
    intro T S h
    obtain ⟨e⟩ := (code_eq_iff_iso T S).mp h
    exact Fintype.card_congr (internalEquiv e))

/-- A358587 counts actual unordered rooted-tree classes with vertex-height equal to internal count. -/
def a (n : ℕ) : ℕ :=
  Fintype.card {T : TreeClass n // classHeight T = classInternalCount T}

#print axioms reaches_depth
#print axioms depth_le
#print axioms depth_root
#print axioms depth_parent
#print axioms code_eq_iff_iso

end

end D5.S3.Combinatorics.UnorderedTrees.ParentTree
