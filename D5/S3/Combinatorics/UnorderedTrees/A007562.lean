/- GID: D5/S3/Combinatorics/UnorderedTrees/A007562
   generality: G
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/A007562
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A size-preserving bijection for the two rooted tree counts in OEIS A007562. -/

import D5.S3.Combinatorics.UnorderedTrees.ParentTree

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

end

end D5.S3.Combinatorics.UnorderedTrees.A007562
