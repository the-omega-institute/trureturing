/- GID: D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/IntervalForestBasic
   mirror-E: none(waiver:general-priority-lattice-counting)
   anchors: []
   utility: none
   digest: Priority-forest interval structure and counting. -/

/-
admission_basis: escape-witness
escape_witness: increasing_tree_card
The tree-code equivalence constructs valid interval trees using the recursive connectivity proof raw_connected_zero.
Direct frozen dependencies: none; direct D5 dependencies are supplied by this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14955
Proof shapes expand all same-delivery declarations and apply the upstream-only bypass test.
IntervalForest: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.addBelow
IntervalForest.ext: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.eq_of_same_support_below
IntervalForest.edges: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.le_iff_parent
IntervalForest.edges_injective: proof_shape: bind-only; consumer: IntervalForestBasic.IntervalForest.forestPartialOrder
IntervalForest.forestPartialOrder: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.addBelow
IntervalForest.forestFinite: proof_shape: bind-only; consumer: ForestCovers.filter_iso_rank
filterCount: proof_shape: bind-only; consumer: PrincipalFilters.result
idealCount: proof_shape: bind-only; consumer: PrincipalIdeals.IdealCount.idealCountResult
positiveIdealCount: proof_shape: bind-only; consumer: PrincipalIdeals.IdealCount.idealCountResult
IntervalForest.connected: proof_shape: bind-only; consumer: IntervalForestBasic.IntervalForest.connected_iff_root_eq
IntervalForest.empty: proof_shape: bind-only; consumer: ForestCovers.rank_bot
IntervalForest.forestBot: proof_shape: bind-only; consumer: ForestCovers.rank_bot
IntervalForest.forestOrderBot: proof_shape: bind-only; consumer: ForestCovers.filter_iso_rank
IntervalForest.parent_zero: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.edgeCount_eq_iff_tree
IntervalForest.forestNonempty: proof_shape: bind-only; consumer: IntervalForestBasic.IntervalForest.card_zero
IntervalForest.forestZeroSubsingleton: proof_shape: bind-only; consumer: IntervalForestBasic.IntervalForest.card_zero
IntervalForest.card_zero: proof_shape: bind-only; consumer: IdealCompression.pi_zero_card
IntervalForest.root: proof_shape: bind-only; consumer: IntervalForestBasic.IntervalForest.connected_iff_root_eq
IntervalForest.root_eq_of_parent: proof_shape: bind-only; consumer: IntervalForestBasic.IntervalForest.connected_iff_root_eq
IntervalForest.root_eq_self_of_none: proof_shape: bind-only; consumer: IntervalForestBasic.IntervalForest.connected_root
IntervalForest.connected_root: proof_shape: content
IntervalForest.root_le: proof_shape: content
IntervalForest.parent_root: proof_shape: content
IntervalForest.connected_iff_root_eq: proof_shape: content
IntervalForest.root_monotone: proof_shape: content
IntervalForest.no_skipped_root: proof_shape: content
rawRoot: proof_shape: bind-only; consumer: IntervalForestBasic.forestOfLocal
raw_root_le: proof_shape: content
raw_root_none: proof_shape: content
raw_root_connected: proof_shape: content
raw_connected_iff: proof_shape: content
root_of_root_le: proof_shape: content
raw_root_monotone: proof_shape: content
forestOfLocal: proof_shape: content
IsTree: proof_shape: bind-only; consumer: ForestCovers.IntervalForest.edgeCount_eq_iff_tree
raw_connected_zero: proof_shape: content
treeCodeParent: proof_shape: bind-only; consumer: IntervalForestBasic.treeCodeParent_increasing
treeCodeParent_increasing: proof_shape: bind-only; consumer: IntervalForestBasic.treeCodeToForest
treeCodeParent_roots: proof_shape: bind-only; consumer: IntervalForestBasic.treeCodeToForest
treeCodeToForest: proof_shape: content
treeCodeToForest_tree: proof_shape: bind-only; consumer: IntervalForestBasic.treeEquivCode
tree_parent_exists: proof_shape: bind-only; consumer: IntervalForestBasic.treeToCode
treeToCode: proof_shape: bind-only; consumer: IntervalForestBasic.treeEquivCode
treeToCode_parent: proof_shape: bind-only; consumer: IntervalForestBasic.tree_code_left_inv
tree_code_left_inv: proof_shape: bind-only; consumer: IntervalForestBasic.treeEquivCode
tree_code_right_inv: proof_shape: bind-only; consumer: IntervalForestBasic.treeEquivCode
treeEquivCode: proof_shape: content
increasing_tree_card: proof_shape: content
-/

import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Nat.Factorial.BigOperators



namespace D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest
end D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest
open D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic.IntervalForest

namespace D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic

structure IntervalForest (n : Nat) where
  parent : Fin (n + 1) -> Option (Fin (n + 1))
  increasing : forall v p, parent v = some p -> p < v
  intervals : forall u v w : Fin (n + 1), u <= v -> v <= w ->
    Relation.EqvGen (fun a b => parent b = some a) u w ->
    Relation.EqvGen (fun a b => parent b = some a) u v

namespace IntervalForest

@[ext] theorem ext {n : Nat} {P Q : IntervalForest n}
    (h : P.parent = Q.parent) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

def edges {n : Nat} (P : IntervalForest n) : Set (Fin (n+1) × Fin (n+1)) :=
  {e | P.parent e.2 = some e.1}

theorem edges_injective {n : Nat} : Function.Injective (@edges n) := by
  intro P Q h
  apply ext
  funext v
  have hv : forall p, P.parent v = some p <-> Q.parent v = some p := by
    intro p
    exact Set.ext_iff.mp h (p,v)
  cases hp : P.parent v with
  | none =>
    cases hq : Q.parent v with
    | none => rfl
    | some p => exact (by simpa [hp] using (hv p).mpr hq)
  | some p => exact (hv p).mp hp |>.symm

instance forestPartialOrder (n : Nat) : PartialOrder (IntervalForest n) :=
  PartialOrder.lift edges edges_injective

private instance forestFinite (n : Nat) : Finite (IntervalForest n) :=
  Finite.of_injective IntervalForest.parent (by intro P Q h; exact ext h)

end IntervalForest



noncomputable def filterCount (n : Nat) : Nat :=
  Nat.card {x : (WithTop (IntervalForest n)) // ∃ m ≤ n, Nonempty (Set.Ici x ≃o (WithTop (IntervalForest m)))}

noncomputable def idealCount (n : Nat) : Nat :=
  Nat.card {x : (WithTop (IntervalForest n)) // ∃ m ≤ n, Nonempty (Set.Iic x ≃o (WithTop (IntervalForest m)))}

noncomputable def positiveIdealCount (n : Nat) : Nat :=
  Nat.card {x : (WithTop (IntervalForest n)) // exists m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic x ≃o (WithTop (IntervalForest m)))}

end D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic

namespace D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
namespace IntervalForest

variable {n : Nat}

private def connected (P : IntervalForest n) :=
  Relation.EqvGen (fun a b => P.parent b = some a)

def empty (n : Nat) : IntervalForest n where
  parent := fun _ => none
  increasing := by simp
  intervals := by
    intro u v w huv hvw h
    have hempty : forall a b : Fin (n+1),
        Relation.EqvGen (fun a _ => (none : Option (Fin (n+1))) = some a) a b -> a = b := by
      intro a b hab
      induction hab with
      | rel x y h => cases h
      | refl x => rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    have huw : u = w := hempty u w h
    have huv' : u = v := le_antisymm huv (huw ▸ hvw)
    subst v
    exact Relation.EqvGen.refl _

private instance forestBot (n : Nat) : Bot (IntervalForest n) := ⟨empty n⟩

private instance forestOrderBot (n : Nat) : OrderBot (IntervalForest n) where
  bot_le := by intro P e h; cases h

theorem parent_zero (P : IntervalForest n) : P.parent 0 = none := by
  cases h : P.parent 0 with
  | none => rfl
  | some p => have hp := P.increasing 0 p h; exact (not_lt_of_ge (Fin.zero_le _) hp).elim

private instance forestNonempty (n : Nat) : Nonempty (IntervalForest n) := ⟨empty n⟩

private instance forestZeroSubsingleton : Subsingleton (IntervalForest 0) where
  allEq P Q := by
    apply ext
    funext v
    have hv : v = 0 := by apply Fin.ext; omega
    subst v
    rw [parent_zero, parent_zero]

@[simp] theorem card_zero : Nat.card (IntervalForest 0) = 1 := by
  exact Nat.card_unique

private noncomputable def root (P : IntervalForest n) (v : Fin (n+1)) : Fin (n+1) :=
  match h : P.parent v with
  | none => v
  | some p => root P p
termination_by v.val
decreasing_by exact P.increasing v p h

private theorem root_eq_of_parent {P : IntervalForest n} {v p : Fin (n+1)}
    (h : P.parent v = some p) : P.root v = P.root p := by
  rw [root, h]

private theorem root_eq_self_of_none {P : IntervalForest n} {v : Fin (n+1)}
    (h : P.parent v = none) : P.root v = v := by
  rw [root, h]

private theorem connected_root (P : IntervalForest n) (v : Fin (n+1)) : P.connected (P.root v) v := by
  cases h : P.parent v with
  | none => rw [root_eq_self_of_none h]; exact Relation.EqvGen.refl _
  | some p =>
    rw [root_eq_of_parent h]
    exact Relation.EqvGen.trans _ _ _ (connected_root P p) (Relation.EqvGen.rel _ _ h)
termination_by v.val
decreasing_by exact P.increasing v p h

private theorem root_le (P : IntervalForest n) (v : Fin (n+1)) : P.root v <= v := by
  cases h : P.parent v with
  | none => rw [root_eq_self_of_none h]
  | some p =>
    rw [root_eq_of_parent h]
    exact (root_le P p).trans (P.increasing v p h).le
termination_by v.val
decreasing_by exact P.increasing v p h

private theorem parent_root (P : IntervalForest n) (v : Fin (n+1)) : P.parent (P.root v) = none := by
  cases h : P.parent v with
  | none => rwa [root_eq_self_of_none h]
  | some p => rw [root_eq_of_parent h]; exact parent_root P p
termination_by v.val
decreasing_by exact P.increasing v p h

private theorem connected_iff_root_eq (P : IntervalForest n) (u v : Fin (n+1)) :
    P.connected u v <-> P.root u = P.root v := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact (root_eq_of_parent h).symm
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (connected_root P u))
      (h ▸ connected_root P v)

private theorem root_monotone (P : IntervalForest n) : Monotone P.root := by
  intro u v huv
  by_cases h : P.root v <= u
  · have hconn := P.intervals (P.root v) u v h huv (connected_root P v)
    have heq := (connected_iff_root_eq P (P.root v) u).mp hconn
    rw [root_eq_self_of_none (parent_root P v)] at heq
    exact le_of_eq heq.symm
  · exact (root_le P u).trans (le_of_lt (lt_of_not_ge h))

end IntervalForest
end D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic

namespace D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
namespace IntervalForest

variable {n : Nat}

theorem no_skipped_root (P : IntervalForest n) {v p w : Fin (n+1)}
    (hp : P.parent v = some p) (hpw : p < w) (hwv : w <= v) :
    P.parent w ≠ none := by
  intro hw
  have hrp := P.root_eq_of_parent hp
  have hlow : P.root p <= P.root w := P.root_monotone hpw.le
  have hhigh : P.root w <= P.root p := (P.root_monotone hwv).trans_eq hrp
  have heq := le_antisymm hlow hhigh
  rw [P.root_eq_self_of_none hw] at heq
  exact (not_lt_of_ge (heq ▸ P.root_le p)) hpw

end IntervalForest

private noncomputable def rawRoot
    (f : Fin (n+1) -> Option (Fin (n+1)))
    (inc : forall v p, f v = some p -> p < v)
    (v : Fin (n+1)) : Fin (n+1) :=
  match h : f v with
  | none => v
  | some p => rawRoot f inc p
termination_by v.val
decreasing_by exact inc v p h

variable (f : Fin (n+1) -> Option (Fin (n+1)))
    (inc : forall v p, f v = some p -> p < v)

private theorem raw_root_le (v : Fin (n+1)) : rawRoot f inc v <= v := by
  cases h : f v with
  | none => rw [rawRoot, h]
  | some p => rw [rawRoot, h]; exact (raw_root_le p).trans (inc v p h).le
termination_by v.val
decreasing_by exact inc v p h

private theorem raw_root_none (v : Fin (n+1)) : f (rawRoot f inc v) = none := by
  cases h : f v with
  | none => rwa [rawRoot, h]
  | some p => rw [rawRoot, h]; exact raw_root_none p
termination_by v.val
decreasing_by exact inc v p h

private theorem raw_root_connected (v : Fin (n+1)) :
    Relation.EqvGen (fun a b => f b = some a) (rawRoot f inc v) v := by
  cases h : f v with
  | none => rw [rawRoot, h]; exact Relation.EqvGen.refl _
  | some p =>
    rw [rawRoot, h]
    exact Relation.EqvGen.trans _ _ _ (raw_root_connected p) (Relation.EqvGen.rel _ _ h)
termination_by v.val
decreasing_by exact inc v p h

private theorem raw_connected_iff (u v : Fin (n+1)) :
    Relation.EqvGen (fun a b => f b = some a) u v <-> rawRoot f inc u = rawRoot f inc v := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
      have he : rawRoot f inc y = rawRoot f inc x := by rw [rawRoot, h]
      exact he.symm
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (raw_root_connected f inc u))
      (h ▸ raw_root_connected f inc v)

variable (nskip : forall v p w, f v = some p -> p < w -> w <= v -> f w ≠ none)
include nskip

private theorem root_of_root_le (v w : Fin (n+1)) (hw : w <= v) (hr : f w = none) :
    w <= rawRoot f inc v := by
  cases h : f v with
  | none => rwa [rawRoot, h]
  | some p =>
    rw [rawRoot, h]
    have hwp : w <= p := by
      by_contra hwp
      exact nskip v p w h (lt_of_not_ge hwp) hw hr
    exact root_of_root_le p w hwp hr
termination_by v.val
decreasing_by exact inc v p h

private theorem raw_root_monotone : Monotone (rawRoot f inc) := by
  intro u v huv
  exact root_of_root_le f inc nskip v (rawRoot f inc u) ((raw_root_le f inc u).trans huv)
    (raw_root_none f inc u)

def forestOfLocal : IntervalForest n where
  parent := f
  increasing := inc
  intervals := by
    intro u v w huv hvw h
    apply (raw_connected_iff f inc u v).mpr
    have huw := (raw_connected_iff f inc u w).mp h
    have h1 := raw_root_monotone f inc nskip huv
    have h2 := raw_root_monotone f inc nskip hvw
    exact le_antisymm h1 (h2.trans_eq huw.symm)

end D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic

namespace D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic

variable {n : Nat}


def IsTree (P : IntervalForest n) : Prop := forall v, P.parent v = none -> v = 0

private theorem raw_connected_zero
    (f : Fin (n+1) -> Option (Fin (n+1)))
    (inc : forall v p, f v = some p -> p < v)
    (roots : forall v, f v = none -> v = 0)
    (v : Fin (n+1)) : Relation.EqvGen (fun a b => f b = some a) 0 v := by
  cases h : f v with
  | none => have hv := roots v h; subst v; exact Relation.EqvGen.refl _
  | some p =>
    exact Relation.EqvGen.trans _ _ _
      (raw_connected_zero f inc roots p) (Relation.EqvGen.rel _ _ h)
termination_by v.val
decreasing_by exact inc v p h

private def treeCodeParent (t : ((v : Fin n) -> Fin (v.val + 1))) (v : Fin (n+1)) : Option (Fin (n+1)) :=
  if h : v.val = 0 then none else
    some ⟨(t ⟨v.val-1, by omega⟩).val, by have := (t ⟨v.val-1, by omega⟩).isLt; omega⟩

private theorem treeCodeParent_increasing (t : ((v : Fin n) -> Fin (v.val + 1))) (v p : Fin (n+1))
    (h : (treeCodeParent t) v = some p) : p < v := by
  by_cases hv : v.val = 0
  · simp [treeCodeParent, hv] at h
  · have heq : (⟨(t ⟨v.val-1, by omega⟩).val, by
        have := (t ⟨v.val-1, by omega⟩).isLt; omega⟩ : Fin (n+1)) = p := by
      simpa only [treeCodeParent, hv, dite_false, Option.some.injEq] using h
    have hlt := (t ⟨v.val-1, by omega⟩).isLt
    change (t ⟨v.val-1, by omega⟩).val < v.val-1+1 at hlt
    apply Fin.lt_def.mpr
    have hp := congrArg Fin.val heq
    dsimp at hp
    omega

private theorem treeCodeParent_roots (t : ((v : Fin n) -> Fin (v.val + 1))) (v : Fin (n+1))
    (h : (treeCodeParent t) v = none) : v = 0 := by
  by_cases hv : v.val = 0
  · exact Fin.ext hv
  · simp [treeCodeParent, hv] at h

private def treeCodeToForest (t : ((v : Fin n) -> Fin (v.val + 1))) : IntervalForest n where
  parent := (treeCodeParent t)
  increasing := (treeCodeParent_increasing t)
  intervals := by
    intro u v w _ _ _
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (raw_connected_zero (treeCodeParent t) (treeCodeParent_increasing t) (treeCodeParent_roots t) u))
      (raw_connected_zero (treeCodeParent t) (treeCodeParent_increasing t) (treeCodeParent_roots t) v)

private theorem treeCodeToForest_tree (t : ((v : Fin n) -> Fin (v.val + 1))) : IsTree (treeCodeToForest t) := (treeCodeParent_roots t)

private theorem tree_parent_exists (T : {P : IntervalForest n // IsTree P}) (v : Fin n) :
    ∃ p, T.val.parent v.succ = some p := by
  cases hp : T.val.parent v.succ with
  | none => have hw := T.property v.succ hp; have := congrArg Fin.val hw; simp at this
  | some p => exact ⟨p, rfl⟩

private noncomputable def treeToCode (T : {P : IntervalForest n // IsTree P}) : ((v : Fin n) -> Fin (v.val + 1)) := fun v =>
  ⟨(tree_parent_exists T v).choose.val, by
    have hp := T.val.increasing v.succ (tree_parent_exists T v).choose (tree_parent_exists T v).choose_spec
    exact hp⟩

private theorem treeToCode_parent (T : {P : IntervalForest n // IsTree P}) (v : Fin n) :
    T.val.parent v.succ = some ⟨(treeToCode T v).val, by
      have h := (treeToCode T v).isLt
      omega⟩ := by
  exact (tree_parent_exists T v).choose_spec

private theorem tree_code_left_inv (t : ((v : Fin n) -> Fin (v.val + 1))) :
    treeToCode ⟨(treeCodeToForest t), (treeCodeToForest_tree t)⟩ = t := by
  funext v
  have h := treeToCode_parent ⟨(treeCodeToForest t), (treeCodeToForest_tree t)⟩ v
  have hs : v.succ.val ≠ 0 := by simp
  change (treeCodeParent t) v.succ = some ⟨(treeToCode ⟨(treeCodeToForest t), (treeCodeToForest_tree t)⟩ v).val, _⟩ at h
  simp only [treeCodeParent, hs, dite_false] at h
  apply Fin.ext
  have hh := congrArg (fun o => o.map Fin.val) h
  simpa using hh.symm

private theorem tree_code_right_inv (T : {P : IntervalForest n // IsTree P}) :
    (⟨(treeCodeToForest (treeToCode T)), (treeCodeToForest_tree (treeToCode T))⟩ :
      {P : IntervalForest n // IsTree P}) = T := by
  apply Subtype.ext
  apply IntervalForest.ext
  funext v
  by_cases hv : v.val = 0
  · have he : v = 0 := Fin.ext hv
    subst v
    rw [IntervalForest.parent_zero, IntervalForest.parent_zero]
  · let w : Fin n := ⟨v.val-1, by omega⟩
    have hw : w.succ = v := by apply Fin.ext; dsimp [w]; omega
    have h := treeToCode_parent T w
    change (treeCodeParent (treeToCode T)) v = T.val.parent v
    unfold treeCodeParent
    rw [dif_neg hv]
    rw [hw] at h
    exact h.symm

noncomputable def treeEquivCode (n : Nat) : {P : IntervalForest n // IsTree P} ≃ ((v : Fin n) -> Fin (v.val + 1)) where
  toFun := treeToCode
  invFun := fun t => ⟨(treeCodeToForest t), (treeCodeToForest_tree t)⟩
  left_inv := tree_code_right_inv
  right_inv := tree_code_left_inv

theorem increasing_tree_card (n : Nat) : Nat.card {P : IntervalForest n // IsTree P} = n.factorial := by
  rw [Nat.card_congr (treeEquivCode n)]
  change Nat.card ((v : Fin n) -> Fin (v.val+1)) = n.factorial
  rw [Nat.card_pi]
  simp only [Nat.card_fin]
  rw [Fin.prod_univ_eq_prod_range (fun i : Nat => i+1) n]
  exact Finset.prod_range_add_one_eq_factorial n

end D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
