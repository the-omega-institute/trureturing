/- GID: D5/S3/Combinatorics/UnorderedTrees/A007562
   generality: G
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/A007562
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A size-preserving bijection for the two rooted tree counts in OEIS A007562. -/

import D5.S3.Combinatorics.UnorderedTrees.ParentTree
import Mathlib.SetTheory.Cardinal.Finite

/-! The bijection reparents vertices on the original carrier, keeping the root fixed. -/

namespace D5.S3.Combinatorics.UnorderedTrees.A007562

open ParentTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The normalized planted condition, allowing the singleton. -/
def ParityTree {V : Type*} (T : Tree V) : Prop :=
  ∀ u, Even (depth T u) → ∀ v w, Child T v u → Child T w u → v = w

/-- The literal planted condition, including the requirement of a root child. -/
def Planted {V : Type*} (T : Tree V) : Prop :=
  (∃! v, Child T v T.root) ∧
    ∀ u, u ≠ T.root → Even (depth T u) → Internal T u → ∃! v, Child T v u

/-- Every internal vertex has an immediate leaf child. -/
def LeafChildTree {V : Type*} (T : Tree V) : Prop :=
  ∀ u, Internal T u → ∃ v, Child T v u ∧ ¬ Internal T v

private theorem depth_pos {V : Type*} (T : Tree V) {v : V} (hv : v ≠ T.root) :
    0 < depth T v := by
  rw [depth_parent T hv]
  exact Nat.zero_lt_succ _

private theorem parent_ne_self {V : Type*} (T : Tree V) {v : V} (hv : v ≠ T.root) :
    T.parent v ≠ v := by
  intro h
  have hd := depth_parent T hv
  rw [h] at hd
  omega

private theorem child_depth {V : Type*} {T : Tree V} {v u : V} (h : Child T v u) :
    depth T v = depth T u + 1 := by
  rw [depth_parent T h.1, h.2]

private theorem reaches_of_rank {V : Type*} (p : V → V) (r : V) (rank : V → ℕ)
    (hpos : ∀ v, v ≠ r → 0 < rank v)
    (hstep : ∀ v, v ≠ r → rank (p v) + 1 = rank v)
    (v : V) : ∃ k, (p^[k]) v = r := by
  generalize hn : rank v = n
  induction n generalizing v with
  | zero =>
    exact ⟨0, by
      change v = r
      by_contra hv
      exact (Nat.ne_of_gt (hpos v hv)) hn⟩
  | succ n ih =>
    by_cases hv : v = r
    · exact ⟨0, hv⟩
    · have hp : rank (p v) = n := Nat.succ.inj ((hstep v hv).trans hn)
      obtain ⟨k, hk⟩ := ih (p v) hp
      exact ⟨k + 1, by rwa [Function.iterate_succ_apply]⟩

private theorem depth_of_rank {V : Type*} (T : Tree V) (rank : V → ℕ)
    (hroot : rank T.root = 0)
    (hstep : ∀ v, v ≠ T.root → rank (T.parent v) + 1 = rank v)
    (v : V) : depth T v = rank v := by
  generalize hn : depth T v = n
  induction n generalizing v with
  | zero =>
    by_cases hv : v = T.root
    · simpa only [hv] using hroot.symm
    · exact ((Nat.ne_of_gt (depth_pos T hv)) hn).elim
  | succ n ih =>
    have hv : v ≠ T.root := by
      intro h
      rw [h, depth_root] at hn
      omega
    have hp : depth T (T.parent v) = n :=
      Nat.succ.inj ((depth_parent T hv).symm.trans hn)
    rw [← hstep v hv, ← ih _ hp]

private theorem tree_eq {V : Type*} {T U : Tree V}
    (hp : T.parent = U.parent) (hr : T.root = U.root) : T = U := by
  cases T
  cases U
  cases hp
  cases hr
  rfl

private def forwardParent {V : Type*} (T : Tree V) (v : V) : V :=
  if v = T.root then T.root
  else if Even (depth T v) then T.parent (T.parent v) else T.parent v

private def forwardRank {V : Type*} (T : Tree V) (v : V) : ℕ :=
  (depth T v + 1) / 2

private theorem forward_rank_step {V : Type*} (T : Tree V) (v : V)
    (hv : v ≠ T.root) :
    forwardRank T (forwardParent T v) + 1 = forwardRank T v := by
  have hd := depth_parent T hv
  by_cases he : Even (depth T v)
  · have hmod := Nat.even_iff.mp he
    have hp : T.parent v ≠ T.root := by
      intro h
      rw [h, depth_root] at hd
      omega
    have hdp := depth_parent T hp
    simp only [forwardParent, ite_eq_right hv, ite_eq_left he, forwardRank]
    omega
  · have hmod := Nat.even_iff.not.mp he
    simp only [forwardParent, ite_eq_right hv, ite_eq_right he, forwardRank]
    omega

private def forward {V : Type*} (T : Tree V) : Tree V where
  parent := forwardParent T
  root := T.root
  fixed_root := by simp [forwardParent]
  reaches := reaches_of_rank (forwardParent T) T.root (forwardRank T)
    (fun v hv => by
      have := depth_pos T hv
      unfold forwardRank
      omega)
    (forward_rank_step T)

private theorem forward_depth {V : Type*} (T : Tree V) (v : V) :
    depth (forward T) v = (depth T v + 1) / 2 :=
  depth_of_rank (forward T) (forwardRank T)
    (by change (depth T T.root + 1) / 2 = 0; rw [depth_root]) (forward_rank_step T) v

private theorem even_forward_parent {V : Type*} (T : Tree V) {v : V} (hv : v ≠ T.root) :
    Even (depth T ((forward T).parent v)) := by
  have hd := depth_parent T hv
  by_cases he : Even (depth T v)
  · have hmod := Nat.even_iff.mp he
    have hp : T.parent v ≠ T.root := by
      intro h
      rw [h, depth_root] at hd
      omega
    have hdp := depth_parent T hp
    change Even (depth T (forwardParent T v))
    simp only [forwardParent, ite_eq_right hv, ite_eq_left he]
    rw [Nat.even_iff]
    omega
  · have hmod := Nat.even_iff.not.mp he
    change Even (depth T (forwardParent T v))
    simp only [forwardParent, ite_eq_right hv, ite_eq_right he]
    rw [Nat.even_iff]
    omega

private theorem forward_leaf {V : Type*} {T : Tree V} {v : V}
    (ho : ¬ Even (depth T v)) : ¬ Internal (forward T) v := by
  rintro ⟨w, hw⟩
  exact ho (hw.2 ▸ even_forward_parent T hw.1)

private theorem forward_child_of_odd {V : Type*} {T : Tree V} {v u : V}
    (h : Child T v u) (ho : ¬ Even (depth T v)) : Child (forward T) v u := by
  exact ⟨h.1, by simpa only [forward, forwardParent, ite_eq_right h.1, ite_eq_right ho] using h.2⟩

private theorem forward_odd_child {V : Type*} {T : Tree V} {u v : V}
    (he : Even (depth T u)) (h : Child T v u) : ¬ Even (depth T v) := by
  have hd := child_depth h
  rw [Nat.even_iff] at he ⊢
  omega

private theorem original_child_of_forward {V : Type*} {T : Tree V} {u : V}
    (hi : Internal (forward T) u) : Internal T u := by
  obtain ⟨v, hv, hp⟩ := hi
  change v ≠ T.root at hv
  change forwardParent T v = u at hp
  by_cases he : Even (depth T v)
  · have hd := depth_parent T hv
    have hmod := Nat.even_iff.mp he
    have hpne : T.parent v ≠ T.root := by
      intro h
      rw [h, depth_root] at hd
      omega
    exact ⟨T.parent v, hpne, by simpa only [forwardParent, ite_eq_right hv, ite_eq_left he] using hp⟩
  · exact ⟨v, hv, by simpa only [forwardParent, ite_eq_right hv, ite_eq_right he] using hp⟩

private theorem forward_leafChildTree {V : Type*} (T : Tree V) :
    LeafChildTree (forward T) := by
  intro u hu
  obtain ⟨v, hv⟩ := original_child_of_forward hu
  obtain ⟨w, hw⟩ := hu
  have he : Even (depth T u) := hw.2 ▸ even_forward_parent T hw.1
  have ho := forward_odd_child he hv
  exact ⟨v, forward_child_of_odd hv ho, forward_leaf ho⟩

private def forwardIso {V W : Type*} {T : Tree V} {U : Tree W} (e : Iso T U) :
    Iso (forward T) (forward U) where
  equiv := e.equiv
  root_eq := e.root_eq
  parent_eq v := by
    have hr : e.equiv v = U.root ↔ v = T.root :=
      ⟨fun h => e.equiv.injective (h.trans e.root_eq.symm),
        fun h => h ▸ e.root_eq⟩
    change e.equiv (forwardParent T v) = forwardParent U (e.equiv v)
    by_cases hv : v = T.root
    · simp only [forwardParent, ite_eq_left hv, ite_eq_left (hr.mpr hv), e.root_eq]
    · simp only [forwardParent, ite_eq_right hv, ite_eq_right (mt hr.mp hv), iso_depth e]
      split <;> simp only [e.parent_eq]

/-- One selected leaf child at each internal vertex, with the identity on leaves. -/
private structure LeafSelection {V : Type*} (U : Tree V) where
  pick : V → V
  internal : ∀ u, Internal U u → Child U (pick u) u ∧ ¬ Internal U (pick u)
  leaf : ∀ u, ¬ Internal U u → pick u = u

private def chooseLeaves {V : Type*} {U : Tree V} (h : LeafChildTree U) :
    LeafSelection U where
  pick u := if hi : Internal U u then Classical.choose (h u hi) else u
  internal u hi := by simpa only [dite_eq_left hi] using Classical.choose_spec (h u hi)
  leaf u hu := by rw [dite_eq_right hu]

private def Marked {V : Type*} {U : Tree V} (s : LeafSelection U) (v : V) : Prop :=
  v ≠ U.root ∧ s.pick (U.parent v) = v

private theorem internal_parent {V : Type*} {U : Tree V} {v : V} (hv : v ≠ U.root) :
    Internal U (U.parent v) :=
  ⟨v, hv, rfl⟩

private theorem marked_leaf {V : Type*} {U : Tree V} {s : LeafSelection U} {v : V}
    (hm : Marked s v) : ¬ Internal U v := by
  rw [← hm.2]
  exact (s.internal _ (internal_parent hm.1)).2

private theorem marked_pick {V : Type*} {U : Tree V} (s : LeafSelection U) {u : V}
    (hi : Internal U u) : Marked s (s.pick u) := by
  have hc := (s.internal _ hi).1
  exact ⟨hc.1, by rw [hc.2]⟩

private def backwardParent {V : Type*} {U : Tree V} (s : LeafSelection U) (v : V) : V :=
  if v = U.root then U.root
  else if Marked s v then U.parent v else s.pick (U.parent v)

private def backwardRank {V : Type*} {U : Tree V} (s : LeafSelection U) (v : V) : ℕ :=
  2 * depth U v - if Marked s v then 1 else 0

private theorem backward_rank_step {V : Type*} {U : Tree V} (s : LeafSelection U) (v : V)
    (hv : v ≠ U.root) :
    backwardRank s (backwardParent s v) + 1 = backwardRank s v := by
  have hd := depth_parent U hv
  have hi := internal_parent hv
  by_cases hm : Marked s v
  · have hp : ¬ Marked s (U.parent v) := fun hp => marked_leaf hp hi
    simp only [backwardParent, ite_eq_right hv, ite_eq_left hm, backwardRank, ite_eq_right hp]
    omega
  · have hd' := child_depth (s.internal _ hi).1
    simp only [backwardParent, ite_eq_right hv, ite_eq_right hm, backwardRank,
      ite_eq_left (marked_pick s hi), Nat.sub_zero]
    omega

private def backward {V : Type*} {U : Tree V} (s : LeafSelection U) : Tree V where
  parent := backwardParent s
  root := U.root
  fixed_root := by simp [backwardParent]
  reaches := reaches_of_rank (backwardParent s) U.root (backwardRank s)
    (fun v hv => by
      have := depth_pos U hv
      unfold backwardRank
      split <;> omega)
    (backward_rank_step s)

private theorem backward_depth {V : Type*} {U : Tree V} (s : LeafSelection U) (v : V) :
    depth (backward s) v = backwardRank s v :=
  depth_of_rank (backward s) (backwardRank s)
    (by simp [backward, backwardRank, depth_root]) (backward_rank_step s) v

private theorem backward_even_iff {V : Type*} {U : Tree V} (s : LeafSelection U) (v : V) :
    Even (depth (backward s) v) ↔ ¬ Marked s v := by
  rw [backward_depth, Nat.even_iff, backwardRank]
  by_cases hm : Marked s v
  · rw [ite_eq_left hm]
    simp only [hm, not_true_eq_false, iff_false]
    have := depth_pos U hm.1
    omega
  · rw [ite_eq_right hm]
    simp only [Nat.sub_zero, hm, not_false_eq_true, iff_true]
    omega

private theorem backward_child_eq_pick {V : Type*} {U : Tree V} (s : LeafSelection U)
    {v u : V} (hu : ¬ Marked s u) (h : Child (backward s) v u) : v = s.pick u := by
  have hv : v ≠ U.root := h.1
  have hp : backwardParent s v = u := h.2
  rw [backwardParent, ite_eq_right hv] at hp
  by_cases hm : Marked s v
  · rw [ite_eq_left hm] at hp
    exact hm.2.symm.trans (congrArg s.pick hp)
  · rw [ite_eq_right hm] at hp
    exact (hu (hp ▸ marked_pick s (internal_parent hv))).elim

private theorem backward_parityTree {V : Type*} {U : Tree V} (s : LeafSelection U) :
    ParityTree (backward s) := by
  intro u hu v w hv hw
  have h := (backward_even_iff s u).mp hu
  exact (backward_child_eq_pick s h hv).trans (backward_child_eq_pick s h hw).symm

private theorem forward_backward {V : Type*} {U : Tree V} (s : LeafSelection U) :
    forward (backward s) = U := by
  refine tree_eq ?_ rfl
  funext v
  change forwardParent (backward s) v = U.parent v
  by_cases hv : v = U.root
  · rw [forwardParent, ite_eq_left (show v = (backward s).root from hv),
      hv, U.fixed_root]
    rfl
  · have hvr : v ≠ (backward s).root := hv
    rw [forwardParent, ite_eq_right hvr]
    by_cases hm : Marked s v
    · have he : ¬ Even (depth (backward s) v) := fun h => (backward_even_iff s v).mp h hm
      rw [ite_eq_right he]
      change backwardParent s v = U.parent v
      rw [backwardParent, ite_eq_right hv, ite_eq_left hm]
    · have he := (backward_even_iff s v).mpr hm
      have hi := internal_parent hv
      have hc := (s.internal _ hi).1
      rw [ite_eq_left he]
      change backwardParent s (backwardParent s v) = U.parent v
      have hp : backwardParent s v = s.pick (U.parent v) := by
        rw [backwardParent, ite_eq_right hv, ite_eq_right hm]
      rw [hp, backwardParent, ite_eq_right hc.1, ite_eq_left (marked_pick s hi), hc.2]

private def originalLeaf {V : Type*} (T : Tree V) (u : V) : V :=
  if h : Even (depth T u) ∧ Internal T u then Classical.choose h.2 else u

private theorem originalLeaf_eq {V : Type*} {T : Tree V} (hT : ParityTree T)
    {u v : V} (he : Even (depth T u)) (hc : Child T v u) :
    originalLeaf T u = v := by
  have hi : Internal T u := ⟨v, hc⟩
  rw [originalLeaf, dite_eq_left (show Even (depth T u) ∧ Internal T u from ⟨he, hi⟩)]
  exact hT u he _ _ (Classical.choose_spec hi) hc

private def originalSelection {V : Type*} (T : Tree V) : LeafSelection (forward T) where
  pick := originalLeaf T
  internal u hi := by
    have hT := original_child_of_forward hi
    obtain ⟨w, hw⟩ := hi
    have he : Even (depth T u) := hw.2 ▸ even_forward_parent T hw.1
    rw [originalLeaf, dite_eq_left (show Even (depth T u) ∧ Internal T u from ⟨he, hT⟩)]
    have hc : Child T (Classical.choose hT) u := Classical.choose_spec hT
    have ho := forward_odd_child he hc
    exact ⟨forward_child_of_odd hc ho, forward_leaf ho⟩
  leaf u hu := by
    have hn : ¬ (Even (depth T u) ∧ Internal T u) := by
      rintro ⟨he, v, hv⟩
      exact hu ⟨v, forward_child_of_odd hv (forward_odd_child he hv)⟩
    rw [originalLeaf, dite_eq_right hn]

private theorem backward_forward {V : Type*} {T : Tree V} (hT : ParityTree T) :
    backward (originalSelection T) = T := by
  refine tree_eq ?_ rfl
  funext v
  change backwardParent (originalSelection T) v = T.parent v
  by_cases hv : v = T.root
  · rw [backwardParent, ite_eq_left (show v = (forward T).root from hv),
      hv, T.fixed_root]
    rfl
  · have hr : v ≠ (forward T).root := hv
    rw [backwardParent, ite_eq_right hr]
    have hd := depth_parent T hv
    by_cases he : Even (depth T v)
    · have hp : T.parent v ≠ T.root := by
        have hmod := Nat.even_iff.mp he
        intro h
        rw [h, depth_root] at hd
        omega
      have hdp := depth_parent T hp
      have he' : Even (depth T (T.parent (T.parent v))) := by
        rw [Nat.even_iff] at he ⊢
        omega
      have hq : (forward T).parent v = T.parent (T.parent v) := by
        exact ite_eq_right hv |>.trans (ite_eq_left he)
      have hs : (originalSelection T).pick ((forward T).parent v) = T.parent v := by
        change originalLeaf T ((forward T).parent v) = T.parent v
        rw [hq]
        exact originalLeaf_eq hT he' ⟨hp, rfl⟩
      have hm : ¬ Marked (originalSelection T) v :=
        fun h => parent_ne_self T hv (hs.symm.trans h.2)
      rw [ite_eq_right hm, hs]
    · have he' : Even (depth T (T.parent v)) := by
        rw [Nat.even_iff] at he ⊢
        omega
      have hq : (forward T).parent v = T.parent v := by
        exact ite_eq_right hv |>.trans (ite_eq_right he)
      have hs : (originalSelection T).pick ((forward T).parent v) = v := by
        change originalLeaf T ((forward T).parent v) = v
        rw [hq]
        exact originalLeaf_eq hT he' ⟨hv, rfl⟩
      rw [ite_eq_left (show Marked (originalSelection T) v from ⟨hr, hs⟩), hq]

private def selectionSwap {V : Type*} {U : Tree V} (s t : LeafSelection U) (v : V) : V :=
  if v = U.root then v else Equiv.swap (s.pick (U.parent v)) (t.pick (U.parent v)) v

private theorem selectionSwap_parent {V : Type*} {U : Tree V} (s t : LeafSelection U)
    (v : V) : U.parent (selectionSwap s t v) = U.parent v := by
  by_cases hv : v = U.root
  · rw [selectionSwap, ite_eq_left hv]
  · have hi := internal_parent hv
    rw [selectionSwap, ite_eq_right hv]
    exact Equiv.apply_swap_eq_self ((s.internal _ hi).1.2.trans (t.internal _ hi).1.2.symm) v

private theorem selectionSwap_nonroot {V : Type*} {U : Tree V} (s t : LeafSelection U)
    {v : V} (hv : v ≠ U.root) : selectionSwap s t v ≠ U.root := by
  have hi := internal_parent hv
  rw [selectionSwap, ite_eq_right hv, Equiv.swap_apply_def]
  split
  · exact (t.internal _ hi).1.1
  · split
    · exact (s.internal _ hi).1.1
    · exact hv

private theorem selectionSwap_involutive {V : Type*} {U : Tree V}
    (s t : LeafSelection U) : Function.Involutive (selectionSwap s t) := by
  intro v
  by_cases hv : v = U.root
  · subst v
    simp [selectionSwap]
  · rw [selectionSwap, ite_eq_right (selectionSwap_nonroot s t hv), selectionSwap_parent,
      selectionSwap, ite_eq_right hv, Equiv.swap_apply_self]

private theorem selectionSwap_internal {V : Type*} {U : Tree V} (s t : LeafSelection U)
    {u : V} (hu : Internal U u) : selectionSwap s t u = u := by
  by_cases hv : u = U.root
  · rw [selectionSwap, ite_eq_left hv]
  · have hi := internal_parent hv
    rw [selectionSwap, ite_eq_right hv]
    apply Equiv.swap_apply_of_ne_of_ne
    · exact fun h => (s.internal _ hi).2 (h ▸ hu)
    · exact fun h => (t.internal _ hi).2 (h ▸ hu)

private theorem selectionSwap_pick {V : Type*} {U : Tree V} (s t : LeafSelection U)
    {u : V} (hu : Internal U u) : selectionSwap s t (s.pick u) = t.pick u := by
  have hc := (s.internal u hu).1
  rw [selectionSwap, ite_eq_right hc.1, hc.2, Equiv.swap_apply_left]

private def selectionIso {V : Type*} {U : Tree V} (s t : LeafSelection U) :
    Iso (backward s) (backward t) where
  equiv := (selectionSwap_involutive s t).toPerm _
  root_eq := by change selectionSwap s t U.root = U.root; simp [selectionSwap]
  parent_eq v := by
    change selectionSwap s t (backwardParent s v) = backwardParent t (selectionSwap s t v)
    by_cases hv : v = U.root
    · subst v
      simp [backwardParent, selectionSwap]
    · have hh := selectionSwap_nonroot s t hv
      have hi := internal_parent hv
      have hp := selectionSwap_parent s t v
      have hs := selectionSwap_pick s t hi
      have hm : Marked t (selectionSwap s t v) ↔ Marked s v := by
        change (selectionSwap s t v ≠ U.root ∧
          t.pick (U.parent (selectionSwap s t v)) = selectionSwap s t v) ↔
          (v ≠ U.root ∧ s.pick (U.parent v) = v)
        rw [hp, ← hs]
        rw [(selectionSwap_involutive s t).injective.eq_iff]
        exact ⟨fun h => ⟨hv, h.2⟩, fun h => ⟨hh, h.2⟩⟩
      simp only [backwardParent, ite_eq_right hv, ite_eq_right hh, hp]
      by_cases h : Marked s v
      · rw [ite_eq_left h, ite_eq_left (hm.mpr h), selectionSwap_internal s t hi]
      · rw [ite_eq_right h, ite_eq_right (mt hm.mp h), hs]

private def transportSelection {V W : Type*} {T : Tree V} {U : Tree W}
    (e : Iso T U) (s : LeafSelection T) : LeafSelection U where
  pick w := e.equiv (s.pick (e.equiv.symm w))
  internal w hw := by
    let v := e.equiv.symm w
    have hv : Internal T v := (iso_internal e v).mpr (by simpa [v] using hw)
    obtain ⟨hc, hl⟩ := s.internal v hv
    exact ⟨by simpa [v] using (iso_child e _ v).mp hc, mt (iso_internal e _).mpr hl⟩
  leaf w hw := by
    have hv : ¬ Internal T (e.equiv.symm w) :=
      mt (iso_internal e (e.equiv.symm w)).mp (by simpa using hw)
    rw [s.leaf _ hv, Equiv.apply_symm_apply]

private def transportBackwardIso {V W : Type*} {T : Tree V} {U : Tree W}
    (e : Iso T U) (s : LeafSelection T) : Iso (backward s) (backward (transportSelection e s)) where
  equiv := e.equiv
  root_eq := e.root_eq
  parent_eq v := by
    change e.equiv (backwardParent s v) = backwardParent (transportSelection e s) (e.equiv v)
    by_cases hv : v = T.root
    · have hw : e.equiv v = U.root := hv ▸ e.root_eq
      rw [backwardParent, ite_eq_left hv, backwardParent, ite_eq_left hw, e.root_eq]
    · have hw : e.equiv v ≠ U.root := fun h => hv (e.equiv.injective (h.trans e.root_eq.symm))
      have hp : (transportSelection e s).pick (U.parent (e.equiv v)) =
          e.equiv (s.pick (T.parent v)) := by
        rw [← e.parent_eq]
        simp only [transportSelection, Equiv.symm_apply_apply]
      have hm : Marked (transportSelection e s) (e.equiv v) ↔ Marked s v := by
        change (e.equiv v ≠ U.root ∧
          (transportSelection e s).pick (U.parent (e.equiv v)) = e.equiv v) ↔
          (v ≠ T.root ∧ s.pick (T.parent v) = v)
        rw [hp, e.equiv.injective.eq_iff]
        exact ⟨fun h => ⟨hv, h.2⟩, fun h => ⟨hw, h.2⟩⟩
      simp only [backwardParent, ite_eq_right hv, ite_eq_right hw]
      by_cases h : Marked s v
      · rw [ite_eq_left h, ite_eq_left (hm.mpr h), e.parent_eq]
      · rw [ite_eq_right h, ite_eq_right (mt hm.mp h), hp]

private def recoverIso {V W : Type*} {T : Tree V} {U : Tree W}
    (hT : ParityTree T) (hU : ParityTree U) (e : Iso (forward T) (forward U)) : Iso T U := by
  simpa only [backward_forward hT, backward_forward hU] using
    (transportBackwardIso e (originalSelection T)).trans
      (selectionIso (transportSelection e (originalSelection T)) (originalSelection U))

private theorem parityTree_iso {V W : Type*} {T : Tree V} {U : Tree W}
    (e : Iso T U) (hT : ParityTree T) : ParityTree U := by
  intro u he v w hv hw
  have hu : Even (depth T (e.equiv.symm u)) := by
    rw [← iso_depth e, Equiv.apply_symm_apply]
    exact he
  apply e.equiv.symm.injective
  exact hT _ hu _ _ ((iso_child e.symm _ _).mp hv) ((iso_child e.symm _ _).mp hw)

private theorem leafChildTree_iso {V W : Type*} {T : Tree V} {U : Tree W}
    (e : Iso T U) (hT : LeafChildTree T) : LeafChildTree U := by
  intro u hi
  obtain ⟨v, hc, hl⟩ := hT _ ((iso_internal e.symm _).mp hi)
  refine ⟨e.equiv v, ?_, mt (iso_internal e v).mpr hl⟩
  simpa only [Iso.symm, Equiv.apply_symm_apply] using (iso_child e _ _).mp hc

private theorem unique_child {V : Type*} {T : Tree V} (h : ParityTree T)
    {u : V} (he : Even (depth T u)) (hi : Internal T u) : ∃! v, Child T v u := by
  obtain ⟨v, hv⟩ := hi
  exact ⟨v, hv, fun w hw => h u he w v hw hv⟩

private theorem planted_iff {V : Type*} (T : Tree V) :
    Planted T ↔ ParityTree T ∧ Internal T T.root := by
  constructor
  · intro ⟨hr, h⟩
    refine ⟨fun u he v w hv hw => ?_, hr.exists⟩
    by_cases hu : u = T.root
    · subst u
      exact hr.unique hv hw
    · exact (h u hu he ⟨v, hv⟩).unique hv hw
  · intro ⟨h, hr⟩
    have he : Even (depth T T.root) := by rw [depth_root]; exact ⟨0, rfl⟩
    exact ⟨unique_child h he hr, fun _ _ hEven hi => unique_child h hEven hi⟩

private theorem planted_iso {V W : Type*} {T : Tree V} {U : Tree W}
    (e : Iso T U) (hT : Planted T) : Planted U := by
  obtain ⟨h, hr⟩ := (planted_iff T).mp hT
  exact (planted_iff U).mpr ⟨parityTree_iso e h, e.root_eq ▸ (iso_internal e _).mp hr⟩

private theorem root_internal {V : Type*} (T : Tree V) (hV : ∃ v, v ≠ T.root) :
    Internal T T.root := by
  obtain ⟨v, hv⟩ := hV
  obtain ⟨k, hk⟩ := T.reaches v
  induction k generalizing v with
  | zero => exact (hv hk).elim
  | succ k ih =>
    by_cases hp : T.parent v = T.root
    · exact ⟨v, hv, hp⟩
    · exact ih _ hp (by simpa only [Function.iterate_succ_apply] using hk)

private def classProperty {n : ℕ} (P : Tree (Fin n) → Prop)
    (inv : ∀ {T U : Tree (Fin n)}, Iso T U → P T → P U) : TreeClass n → Prop :=
  Quotient.lift P (fun T U h => by
    obtain ⟨e⟩ := (code_eq_iff_iso T U).mp h
    exact propext ⟨inv e, inv e.symm⟩)

/-- The actual size-`n` isomorphism classes satisfying the normalized parity condition. -/
def ParityClass (n : ℕ) := {x : TreeClass n // classProperty ParityTree parityTree_iso x}

/-- The actual size-`n` isomorphism classes satisfying the literal planted condition. -/
def PlantedClass (n : ℕ) := {x : TreeClass n // classProperty Planted planted_iso x}

/-- The actual size-`n` isomorphism classes in which each internal vertex has a leaf child. -/
def LeafChildClass (n : ℕ) := {x : TreeClass n // classProperty LeafChildTree leafChildTree_iso x}

private def forwardClass {n : ℕ} : TreeClass n → TreeClass n :=
  Quotient.map forward (fun T U h => by
    obtain ⟨e⟩ := (code_eq_iff_iso T U).mp h
    exact (code_eq_iff_iso _ _).mpr ⟨forwardIso e⟩)

private def classMap (n : ℕ) (x : ParityClass n) : LeafChildClass n :=
  ⟨forwardClass x.1, by
    rcases x with ⟨x, hx⟩
    induction x using Quotient.inductionOn with
    | _ T => exact forward_leafChildTree T⟩

private theorem classMap_bijective (n : ℕ) : Function.Bijective (classMap n) := by
  constructor
  · intro ⟨x, hx⟩ ⟨y, hy⟩ e
    apply Subtype.ext
    have h : forwardClass x = forwardClass y := congrArg Subtype.val e
    clear e
    revert hx hy h
    refine Quotient.inductionOn₂ x y ?_
    intro T U hT hU h
    have hcode := Quotient.exact (s := treeSetoid n) h
    obtain ⟨f⟩ := (code_eq_iff_iso (forward T) (forward U)).mp hcode
    exact Quotient.sound (s := treeSetoid n) ((code_eq_iff_iso T U).mpr ⟨recoverIso hT hU f⟩)
  · intro ⟨y, hy⟩
    revert hy
    refine Quotient.inductionOn y ?_
    intro U (hU : LeafChildTree U)
    let s := chooseLeaves hU
    refine ⟨⟨Quotient.mk _ (backward s), backward_parityTree s⟩, ?_⟩
    apply Subtype.ext
    change Quotient.mk (treeSetoid n) (forward (backward s)) = Quotient.mk (treeSetoid n) U
    rw [forward_backward]

/-- The size-preserving equivalence induced by the forward reparenting on actual classes. -/
def classEquiv (n : ℕ) : ParityClass n ≃ LeafChildClass n :=
  Equiv.ofBijective (classMap n) (classMap_bijective n)

private def plantedEquiv (n : ℕ) (hn : 2 ≤ n) : PlantedClass n ≃ ParityClass n := by
  apply (Equiv.refl (TreeClass n)).subtypeEquiv
  intro x
  refine Quotient.inductionOn x ?_
  intro T
  change Planted T ↔ ParityTree T
  rw [planted_iff, and_iff_left]
  apply root_internal
  apply Fintype.exists_ne_of_one_lt_card
  rw [Fintype.card_fin]
  omega

private instance finiteParityClass (n : ℕ) : Finite (ParityClass n) := by
  unfold ParityClass
  infer_instance

private instance finitePlantedClass (n : ℕ) : Finite (PlantedClass n) := by
  unfold PlantedClass
  infer_instance

private instance finiteLeafChildClass (n : ℕ) : Finite (LeafChildClass n) := by
  unfold LeafChildClass
  infer_instance

/-- The literal planted count, with value zero on one vertex. -/
def plantedCount (n : ℕ) : ℕ := Nat.card (PlantedClass n)

/-- The normalized left count, including the singleton representative. -/
def normalizedCount (n : ℕ) : ℕ := Nat.card (ParityClass n)

/-- The count of rooted trees whose internal vertices have immediate leaf children. -/
def leafChildCount (n : ℕ) : ℕ := Nat.card (LeafChildClass n)

private def singletonTree : Tree (Fin 1) where
  parent := id
  root := 0
  fixed_root := rfl
  reaches v := ⟨0, Subsingleton.elim v 0⟩

private theorem no_singleton_child (T : Tree (Fin 1)) (v u : Fin 1) :
    ¬ Child T v u :=
  fun h => h.1 (Subsingleton.elim v T.root)

private theorem singletonClass_unique (x : TreeClass 1) :
    x = Quotient.mk (treeSetoid 1) singletonTree := by
  refine Quotient.inductionOn x ?_
  intro T
  apply Quotient.sound
  exact (code_eq_iff_iso _ _).mpr
    ⟨⟨Equiv.refl _, Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩⟩

private theorem plantedCount_one : plantedCount 1 = 0 := by
  let : IsEmpty (PlantedClass 1) := ⟨fun ⟨x, hx⟩ => by
    revert hx
    refine Quotient.inductionOn x ?_
    intro T (hT : Planted T)
    obtain ⟨v, hv⟩ := hT.1.exists
    exact no_singleton_child T v T.root hv⟩
  exact Nat.card_of_isEmpty

private theorem normalizedCount_one : normalizedCount 1 = 1 := by
  let x : ParityClass 1 := ⟨Quotient.mk _ singletonTree, fun u _ v _ hv _ =>
    (no_singleton_child _ v u hv).elim⟩
  let : Unique (ParityClass 1) := ⟨⟨x⟩, fun y => Subtype.ext (singletonClass_unique y.1)⟩
  exact Nat.card_unique

private theorem leafChildCount_eq_normalized (n : ℕ) :
    normalizedCount n = leafChildCount n :=
  Nat.card_congr (classEquiv n)

/-- The literal counts agree above size one. At size one the literal planted class is empty,
while the normalized planted and leaf-child classes each contain the singleton. -/
theorem result :
    (∀ n : ℕ, 2 ≤ n → plantedCount n = leafChildCount n) ∧
    (plantedCount 1 = 0 ∧ normalizedCount 1 = 1 ∧ leafChildCount 1 = 1) ∧
    (∀ n : ℕ, 0 < n → normalizedCount n = leafChildCount n) := by
  refine ⟨fun n hn => ?_, ⟨plantedCount_one, normalizedCount_one, ?_⟩,
    fun n _ => leafChildCount_eq_normalized n⟩
  · exact Nat.card_congr ((plantedEquiv n hn).trans (classEquiv n))
  · exact (leafChildCount_eq_normalized 1).symm.trans normalizedCount_one

#print axioms classEquiv
#print axioms result

end

end D5.S3.Combinatorics.UnorderedTrees.A007562
