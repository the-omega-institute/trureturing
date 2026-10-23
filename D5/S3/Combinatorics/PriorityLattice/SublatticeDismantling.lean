/- GID: D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/SublatticeDismantling
   mirror-E: none(waiver:source-question-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.claim; result=D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.result; claim=D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.claim
   digest: The priority lattice is not always sublattice dismantlable. -/

/-
admission_basis: open-problem-resolution (arXiv:2603.28905v1, Section 6 item 4; Refuted)
escape_witness: none
result: proof_shape: content; the actual Pi(6) ambient sublattice and hereditary restriction refute claim.
All auxiliary declarations are used by the refutation or by its ambient-extremum construction.
Direct frozen public dependencies:
IntervalForestBasic.forestOfLocal; statement_id sha256:fb03350098f2771ceaef963948b7a4910c65d556a7f5f038b06e4989adc24067
ForestCovers.IntervalForest.le_iff_parent; statement_id sha256:c9bd9da94d8db519931cb03b6ea673b2f78c35b33d3374df52d13eb7bf0fd1ac
PrincipalFilters.coreOrderIso; statement_id sha256:945956764415f430f4149af4b031f623b570577e182b9cdac4692d1eea406d8a
-/

import D5.S3.Combinatorics.PriorityLattice.PrincipalFilters
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Grind

namespace D5.S3.Combinatorics.PriorityLattice.SublatticeDismantling

/-- Closure under actual ambient binary extrema, without choosing operations. -/
def AmbientClosed {α : Type*} [PartialOrder α] (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s,
    (∃ m ∈ s, IsGLB {x, y} m) ∧ (∃ j ∈ s, IsLUB {x, y} j)

/-- A finite binary tree of disjoint nonempty sublattice subdivisions. -/
inductive Dismantlable {α : Type*} [PartialOrder α] : Set α → Prop
  | singleton (x : α) : Dismantlable {x}
  | split {s u v : Set α} (closed : AmbientClosed s)
      (union : u ∪ v = s) (disjoint : Disjoint u v)
      (left_nonempty : u.Nonempty) (right_nonempty : v.Nonempty)
      (left_closed : AmbientClosed u) (right_closed : AmbientClosed v)
      (left : Dismantlable u) (right : Dismantlable v) : Dismantlable s

private theorem closed_inter {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : AmbientClosed s) (ht : AmbientClosed t) : AmbientClosed (s ∩ t) := by
  intro x hx y hy
  obtain ⟨⟨m, hm, hglb⟩, ⟨j, hj, hlub⟩⟩ := hs x hx.1 y hy.1
  obtain ⟨⟨m', hm', hglb'⟩, ⟨j', hj', hlub'⟩⟩ := ht x hx.2 y hy.2
  have heqm : m = m' := hglb.unique hglb'
  have heqj : j = j' := hlub.unique hlub'
  exact ⟨⟨m, ⟨hm, heqm ▸ hm'⟩, hglb⟩, ⟨j, ⟨hj, heqj ▸ hj'⟩, hlub⟩⟩

private theorem hereditary {α : Type*} [PartialOrder α] {s : Set α}
    (hs : Dismantlable s) : ∀ {t : Set α}, t ⊆ s → t.Nonempty →
      AmbientClosed t → Dismantlable t := by
  induction hs with
  | singleton x =>
    intro t hsub hne _
    have ht : t = {x} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨by
        obtain ⟨y, hy⟩ := hne
        exact (Set.mem_singleton_iff.mp (hsub hy)) ▸ hy,
      fun y hy => hsub hy⟩
    rw [ht]
    exact Dismantlable.singleton x
  | @split s u v hc hu hd hnu hnv hcu hcv _ _ ihu ihv =>
    intro t hsub hnt hct
    have htu : t ∩ u ⊆ u := Set.inter_subset_right
    have htv : t ∩ v ⊆ v := Set.inter_subset_right
    have hcover : (t ∩ u) ∪ (t ∩ v) = t := by
      rw [← Set.inter_union_distrib_left, hu]
      exact Set.inter_eq_left.mpr hsub
    by_cases hlu : (t ∩ u).Nonempty
    · by_cases hlv : (t ∩ v).Nonempty
      · exact Dismantlable.split hct hcover
          (hd.mono Set.inter_subset_right Set.inter_subset_right) hlu hlv
          (closed_inter hct hcu) (closed_inter hct hcv)
          (ihu htu hlu (closed_inter hct hcu)) (ihv htv hlv (closed_inter hct hcv))
      · have he : t ∩ v = ∅ := Set.not_nonempty_iff_eq_empty.mp hlv
        rw [he, Set.union_empty] at hcover
        exact hcover ▸ ihu htu hlu (closed_inter hct hcu)
    · have he : t ∩ u = ∅ := Set.not_nonempty_iff_eq_empty.mp hlu
      rw [he, Set.empty_union] at hcover
      have hlv : (t ∩ v).Nonempty := hcover.symm ▸ hnt
      exact hcover ▸ ihv htv hlv (closed_inter hct hcv)

private theorem closed_image {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {s : Set α} (hs : AmbientClosed s) : AmbientClosed (e '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨⟨m, hm, hgm⟩, ⟨j, hj, hlj⟩⟩ := hs x hx y hy
  refine ⟨⟨e m, ⟨m, hm, rfl⟩, ?_⟩, ⟨e j, ⟨j, hj, rfl⟩, ?_⟩⟩
  · simpa only [Set.image_pair] using (e.isGLB_image').mpr hgm
  · simpa only [Set.image_pair] using (e.isLUB_image').mpr hlj

private theorem dismantlable_image {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {s : Set α} (hs : Dismantlable s) : Dismantlable (e '' s) := by
  induction hs with
  | singleton x => simpa only [Set.image_singleton] using Dismantlable.singleton (e x)
  | @split s u v hc hu hd hnu hnv hcu hcv _ _ ihu ihv =>
    refine Dismantlable.split (closed_image e hc) ?_ ?_
      (hnu.image e) (hnv.image e) (closed_image e hcu) (closed_image e hcv) ihu ihv
    · rw [← Set.image_union, hu]
    · apply Set.disjoint_left.mpr
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
      have hxy := e.injective he
      subst y
      exact Set.disjoint_left.mp hd hx hy

open IntervalForestBasic
open ForestCovers.IntervalForest
open PrincipalFilters

private abbrev PairCode := Fin 4 × Fin 4
private abbrev Code := Option PairCode

private def parent (a : PairCode) (v : Fin 7) : Option (Fin 7) :=
  match v.val with
  | 1 | 2 => some 0
  | 3 => if a.1 = 0 then none else some ⟨a.1.val - 1, by omega⟩
  | 4 | 5 => some 3
  | 6 => if a.2 = 0 then none else some ⟨a.2.val + 2, by omega⟩
  | _ => none

private theorem parent_increasing : ∀ a v p, parent a v = some p → p < v := by decide

private theorem parent_local : ∀ a v p w, parent a v = some p → p < w → w ≤ v →
    parent a w ≠ none := by decide

private def forest (a : PairCode) : IntervalForest 6 :=
  forestOfLocal (parent a) (parent_increasing a) (parent_local a)

private def embed : Code → WithTop (IntervalForest 6)
  | none => ⊤
  | some a => (forest a : WithTop (IntervalForest 6))

private def cmeet (a b : Fin 4) : Fin 4 := if a = b then a else 0
private abbrev compatible (a b : Fin 4) : Prop := a = 0 ∨ b = 0 ∨ a = b
private def cjoin (a b : Fin 4) : Fin 4 := if a = 0 then b else a

private def meetCode : Code → Code → Code
  | none, b => b
  | a, none => a
  | some a, some b => some (cmeet a.1 b.1, cmeet a.2 b.2)

private def joinCode : Code → Code → Code
  | none, _ => none
  | _, none => none
  | some a, some b =>
      if compatible a.1 b.1 ∧ compatible a.2 b.2 then
        some (cjoin a.1 b.1, cjoin a.2 b.2) else none

private theorem parent_meet : ∀ (a b : PairCode) v p,
    parent (cmeet a.1 b.1, cmeet a.2 b.2) v = some p ↔
      parent a v = some p ∧ parent b v = some p := by decide

private theorem embed_injective : Function.Injective embed := by
  have hp : ∀ a b : PairCode, (∀ v, parent a v = parent b v) → a = b := by decide
  intro a b h
  cases a with
  | none => cases b <;> simp_all [embed]
  | some a =>
    cases b with
    | none => simp [embed] at h
    | some b =>
      have hf : forest a = forest b := WithTop.coe_inj.mp h
      have he : a = b := hp a b (fun v => congrArg (fun f : IntervalForest 6 => f.parent v) hf)
      exact congrArg some he

private theorem meet_extremum (a b : Code) :
    IsGLB {embed a, embed b} (embed (meetCode a b)) := by
  rw [isGLB_iff_le_iff]
  intro z
  simp only [mem_lowerBounds, Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  cases a with
  | none => simp [meetCode, embed]
  | some a =>
    cases b with
    | none => simp [meetCode, embed]
    | some b =>
      induction z using WithTop.recTopCoe with
      | top => simp [meetCode, embed]
      | coe Q =>
        simp only [meetCode, embed, WithTop.coe_le_coe]
        rw [le_iff_parent, le_iff_parent, le_iff_parent]
        change (∀ v p, Q.parent v = some p →
          parent (cmeet a.1 b.1, cmeet a.2 b.2) v = some p) ↔
          (∀ v p, Q.parent v = some p → parent a v = some p) ∧
          (∀ v p, Q.parent v = some p → parent b v = some p)
        constructor
        · intro h
          exact ⟨fun v p hp => ((parent_meet a b v p).mp (h v p hp)).1,
            fun v p hp => ((parent_meet a b v p).mp (h v p hp)).2⟩
        · rintro ⟨ha, hb⟩ v p hp
          exact (parent_meet a b v p).mpr ⟨ha v p hp, hb v p hp⟩

private theorem parent_join : ∀ a b : PairCode,
    compatible a.1 b.1 ∧ compatible a.2 b.2 → ∀ v p,
      parent (cjoin a.1 b.1, cjoin a.2 b.2) v = some p ↔
      parent a v = some p ∨ parent b v = some p := by decide

private theorem parent_compatible : ∀ a b : PairCode,
    (∀ v p q, parent a v = some p → parent b v = some q → p = q) →
    compatible a.1 b.1 ∧ compatible a.2 b.2 := by decide

private theorem join_extremum (a b : Code) :
    IsLUB {embed a, embed b} (embed (joinCode a b)) := by
  rw [isLUB_iff_le_iff]
  intro z
  simp only [mem_upperBounds, Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  cases a with
  | none =>
    simp only [joinCode, embed, top_le_iff]
    constructor
    · intro hz; subst z; exact ⟨rfl, le_top⟩
    · exact fun h => h.1
  | some a =>
    cases b with
    | none =>
      simp only [joinCode, embed, top_le_iff]
      constructor
      · intro hz; subst z; exact ⟨le_top, rfl⟩
      · exact fun h => h.2
    | some b =>
      induction z using WithTop.recTopCoe with
      | top => simp
      | coe Q =>
        by_cases hc : compatible a.1 b.1 ∧ compatible a.2 b.2
        · simp only [joinCode, hc, and_self, if_true, embed, WithTop.coe_le_coe]
          rw [le_iff_parent, le_iff_parent, le_iff_parent]
          change (∀ v p, parent (cjoin a.1 b.1, cjoin a.2 b.2) v = some p →
            Q.parent v = some p) ↔
            (∀ v p, parent a v = some p → Q.parent v = some p) ∧
            (∀ v p, parent b v = some p → Q.parent v = some p)
          constructor
          · intro h
            exact ⟨fun v p hp => h v p ((parent_join a b hc v p).mpr (Or.inl hp)),
              fun v p hp => h v p ((parent_join a b hc v p).mpr (Or.inr hp))⟩
          · rintro ⟨ha, hb⟩ v p hp
            exact ((parent_join a b hc v p).mp hp).elim (ha v p) (hb v p)
        · simp only [joinCode, hc, if_false, embed, WithTop.top_le_iff,
            WithTop.coe_ne_top, WithTop.coe_le_coe, false_iff, not_and]
          intro ha hb
          apply hc
          apply parent_compatible a b
          intro v p q hp hq
          have hpQ := (le_iff_parent _ _).mp ha v p hp
          have hqQ := (le_iff_parent _ _).mp hb v q hq
          exact Option.some.inj (hpQ.symm.trans hqQ)

private theorem witness_closed : AmbientClosed (Set.range embed) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ⟨⟨_, ⟨meetCode a b, rfl⟩, meet_extremum a b⟩,
    ⟨_, ⟨joinCode a b, rfl⟩, join_extremum a b⟩⟩

private theorem colour_constant (c : Code → Bool)
    (hc : ∀ a b, c a = c b →
      c (meetCode a b) = c a ∧ c (joinCode a b) = c a) :
    ∀ a, c a = c (some (0, 0)) := by
  have h1_0 : c (some (0, 0)) = c none →
      c (some (0, 0)) = c (some (0, 0)) ∧ c none = c (some (0, 0)) :=
    hc (some (0, 0)) none
  have h2_0 : c (some (0, 1)) = c none →
      c (some (0, 1)) = c (some (0, 1)) ∧ c none = c (some (0, 1)) :=
    hc (some (0, 1)) none
  have h2_1 : c (some (0, 1)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (0, 1)) ∧ c (some (0, 1)) = c (some (0, 1)) :=
    hc (some (0, 1)) (some (0, 0))
  have h3_0 : c (some (0, 2)) = c none →
      c (some (0, 2)) = c (some (0, 2)) ∧ c none = c (some (0, 2)) :=
    hc (some (0, 2)) none
  have h3_1 : c (some (0, 2)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (0, 2)) ∧ c (some (0, 2)) = c (some (0, 2)) :=
    hc (some (0, 2)) (some (0, 0))
  have h3_2 : c (some (0, 2)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (0, 2)) ∧ c none = c (some (0, 2)) :=
    hc (some (0, 2)) (some (0, 1))
  have h4_0 : c (some (0, 3)) = c none →
      c (some (0, 3)) = c (some (0, 3)) ∧ c none = c (some (0, 3)) :=
    hc (some (0, 3)) none
  have h4_1 : c (some (0, 3)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (0, 3)) ∧ c (some (0, 3)) = c (some (0, 3)) :=
    hc (some (0, 3)) (some (0, 0))
  have h4_2 : c (some (0, 3)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (0, 3)) ∧ c none = c (some (0, 3)) :=
    hc (some (0, 3)) (some (0, 1))
  have h4_3 : c (some (0, 3)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (0, 3)) ∧ c none = c (some (0, 3)) :=
    hc (some (0, 3)) (some (0, 2))
  have h5_0 : c (some (1, 0)) = c none →
      c (some (1, 0)) = c (some (1, 0)) ∧ c none = c (some (1, 0)) :=
    hc (some (1, 0)) none
  have h5_1 : c (some (1, 0)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (1, 0)) ∧ c (some (1, 0)) = c (some (1, 0)) :=
    hc (some (1, 0)) (some (0, 0))
  have h5_2 : c (some (1, 0)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (1, 0)) ∧ c (some (1, 1)) = c (some (1, 0)) :=
    hc (some (1, 0)) (some (0, 1))
  have h5_3 : c (some (1, 0)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (1, 0)) ∧ c (some (1, 2)) = c (some (1, 0)) :=
    hc (some (1, 0)) (some (0, 2))
  have h5_4 : c (some (1, 0)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (1, 0)) ∧ c (some (1, 3)) = c (some (1, 0)) :=
    hc (some (1, 0)) (some (0, 3))
  have h6_0 : c (some (1, 1)) = c none →
      c (some (1, 1)) = c (some (1, 1)) ∧ c none = c (some (1, 1)) :=
    hc (some (1, 1)) none
  have h6_1 : c (some (1, 1)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (1, 1)) ∧ c (some (1, 1)) = c (some (1, 1)) :=
    hc (some (1, 1)) (some (0, 0))
  have h6_2 : c (some (1, 1)) = c (some (0, 1)) →
      c (some (0, 1)) = c (some (1, 1)) ∧ c (some (1, 1)) = c (some (1, 1)) :=
    hc (some (1, 1)) (some (0, 1))
  have h6_3 : c (some (1, 1)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (1, 1)) ∧ c none = c (some (1, 1)) :=
    hc (some (1, 1)) (some (0, 2))
  have h6_4 : c (some (1, 1)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (1, 1)) ∧ c none = c (some (1, 1)) :=
    hc (some (1, 1)) (some (0, 3))
  have h6_5 : c (some (1, 1)) = c (some (1, 0)) →
      c (some (1, 0)) = c (some (1, 1)) ∧ c (some (1, 1)) = c (some (1, 1)) :=
    hc (some (1, 1)) (some (1, 0))
  have h7_0 : c (some (1, 2)) = c none →
      c (some (1, 2)) = c (some (1, 2)) ∧ c none = c (some (1, 2)) :=
    hc (some (1, 2)) none
  have h7_1 : c (some (1, 2)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (1, 2)) ∧ c (some (1, 2)) = c (some (1, 2)) :=
    hc (some (1, 2)) (some (0, 0))
  have h7_2 : c (some (1, 2)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (1, 2)) ∧ c none = c (some (1, 2)) :=
    hc (some (1, 2)) (some (0, 1))
  have h7_3 : c (some (1, 2)) = c (some (0, 2)) →
      c (some (0, 2)) = c (some (1, 2)) ∧ c (some (1, 2)) = c (some (1, 2)) :=
    hc (some (1, 2)) (some (0, 2))
  have h7_4 : c (some (1, 2)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (1, 2)) ∧ c none = c (some (1, 2)) :=
    hc (some (1, 2)) (some (0, 3))
  have h7_5 : c (some (1, 2)) = c (some (1, 0)) →
      c (some (1, 0)) = c (some (1, 2)) ∧ c (some (1, 2)) = c (some (1, 2)) :=
    hc (some (1, 2)) (some (1, 0))
  have h7_6 : c (some (1, 2)) = c (some (1, 1)) →
      c (some (1, 0)) = c (some (1, 2)) ∧ c none = c (some (1, 2)) :=
    hc (some (1, 2)) (some (1, 1))
  have h8_0 : c (some (1, 3)) = c none →
      c (some (1, 3)) = c (some (1, 3)) ∧ c none = c (some (1, 3)) :=
    hc (some (1, 3)) none
  have h8_1 : c (some (1, 3)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (1, 3)) ∧ c (some (1, 3)) = c (some (1, 3)) :=
    hc (some (1, 3)) (some (0, 0))
  have h8_2 : c (some (1, 3)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (1, 3)) ∧ c none = c (some (1, 3)) :=
    hc (some (1, 3)) (some (0, 1))
  have h8_3 : c (some (1, 3)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (1, 3)) ∧ c none = c (some (1, 3)) :=
    hc (some (1, 3)) (some (0, 2))
  have h8_4 : c (some (1, 3)) = c (some (0, 3)) →
      c (some (0, 3)) = c (some (1, 3)) ∧ c (some (1, 3)) = c (some (1, 3)) :=
    hc (some (1, 3)) (some (0, 3))
  have h8_5 : c (some (1, 3)) = c (some (1, 0)) →
      c (some (1, 0)) = c (some (1, 3)) ∧ c (some (1, 3)) = c (some (1, 3)) :=
    hc (some (1, 3)) (some (1, 0))
  have h8_6 : c (some (1, 3)) = c (some (1, 1)) →
      c (some (1, 0)) = c (some (1, 3)) ∧ c none = c (some (1, 3)) :=
    hc (some (1, 3)) (some (1, 1))
  have h8_7 : c (some (1, 3)) = c (some (1, 2)) →
      c (some (1, 0)) = c (some (1, 3)) ∧ c none = c (some (1, 3)) :=
    hc (some (1, 3)) (some (1, 2))
  have h9_0 : c (some (2, 0)) = c none →
      c (some (2, 0)) = c (some (2, 0)) ∧ c none = c (some (2, 0)) :=
    hc (some (2, 0)) none
  have h9_1 : c (some (2, 0)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (2, 0)) ∧ c (some (2, 0)) = c (some (2, 0)) :=
    hc (some (2, 0)) (some (0, 0))
  have h9_2 : c (some (2, 0)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (2, 0)) ∧ c (some (2, 1)) = c (some (2, 0)) :=
    hc (some (2, 0)) (some (0, 1))
  have h9_3 : c (some (2, 0)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (2, 0)) ∧ c (some (2, 2)) = c (some (2, 0)) :=
    hc (some (2, 0)) (some (0, 2))
  have h9_4 : c (some (2, 0)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (2, 0)) ∧ c (some (2, 3)) = c (some (2, 0)) :=
    hc (some (2, 0)) (some (0, 3))
  have h9_5 : c (some (2, 0)) = c (some (1, 0)) →
      c (some (0, 0)) = c (some (2, 0)) ∧ c none = c (some (2, 0)) :=
    hc (some (2, 0)) (some (1, 0))
  have h9_6 : c (some (2, 0)) = c (some (1, 1)) →
      c (some (0, 0)) = c (some (2, 0)) ∧ c none = c (some (2, 0)) :=
    hc (some (2, 0)) (some (1, 1))
  have h9_7 : c (some (2, 0)) = c (some (1, 2)) →
      c (some (0, 0)) = c (some (2, 0)) ∧ c none = c (some (2, 0)) :=
    hc (some (2, 0)) (some (1, 2))
  have h9_8 : c (some (2, 0)) = c (some (1, 3)) →
      c (some (0, 0)) = c (some (2, 0)) ∧ c none = c (some (2, 0)) :=
    hc (some (2, 0)) (some (1, 3))
  have h10_0 : c (some (2, 1)) = c none →
      c (some (2, 1)) = c (some (2, 1)) ∧ c none = c (some (2, 1)) :=
    hc (some (2, 1)) none
  have h10_1 : c (some (2, 1)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (2, 1)) ∧ c (some (2, 1)) = c (some (2, 1)) :=
    hc (some (2, 1)) (some (0, 0))
  have h10_2 : c (some (2, 1)) = c (some (0, 1)) →
      c (some (0, 1)) = c (some (2, 1)) ∧ c (some (2, 1)) = c (some (2, 1)) :=
    hc (some (2, 1)) (some (0, 1))
  have h10_3 : c (some (2, 1)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (2, 1)) ∧ c none = c (some (2, 1)) :=
    hc (some (2, 1)) (some (0, 2))
  have h10_4 : c (some (2, 1)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (2, 1)) ∧ c none = c (some (2, 1)) :=
    hc (some (2, 1)) (some (0, 3))
  have h10_5 : c (some (2, 1)) = c (some (1, 0)) →
      c (some (0, 0)) = c (some (2, 1)) ∧ c none = c (some (2, 1)) :=
    hc (some (2, 1)) (some (1, 0))
  have h10_6 : c (some (2, 1)) = c (some (1, 1)) →
      c (some (0, 1)) = c (some (2, 1)) ∧ c none = c (some (2, 1)) :=
    hc (some (2, 1)) (some (1, 1))
  have h10_7 : c (some (2, 1)) = c (some (1, 2)) →
      c (some (0, 0)) = c (some (2, 1)) ∧ c none = c (some (2, 1)) :=
    hc (some (2, 1)) (some (1, 2))
  have h10_8 : c (some (2, 1)) = c (some (1, 3)) →
      c (some (0, 0)) = c (some (2, 1)) ∧ c none = c (some (2, 1)) :=
    hc (some (2, 1)) (some (1, 3))
  have h10_9 : c (some (2, 1)) = c (some (2, 0)) →
      c (some (2, 0)) = c (some (2, 1)) ∧ c (some (2, 1)) = c (some (2, 1)) :=
    hc (some (2, 1)) (some (2, 0))
  have h11_0 : c (some (2, 2)) = c none →
      c (some (2, 2)) = c (some (2, 2)) ∧ c none = c (some (2, 2)) :=
    hc (some (2, 2)) none
  have h11_1 : c (some (2, 2)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (2, 2)) ∧ c (some (2, 2)) = c (some (2, 2)) :=
    hc (some (2, 2)) (some (0, 0))
  have h11_2 : c (some (2, 2)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (2, 2)) ∧ c none = c (some (2, 2)) :=
    hc (some (2, 2)) (some (0, 1))
  have h11_3 : c (some (2, 2)) = c (some (0, 2)) →
      c (some (0, 2)) = c (some (2, 2)) ∧ c (some (2, 2)) = c (some (2, 2)) :=
    hc (some (2, 2)) (some (0, 2))
  have h11_4 : c (some (2, 2)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (2, 2)) ∧ c none = c (some (2, 2)) :=
    hc (some (2, 2)) (some (0, 3))
  have h11_5 : c (some (2, 2)) = c (some (1, 0)) →
      c (some (0, 0)) = c (some (2, 2)) ∧ c none = c (some (2, 2)) :=
    hc (some (2, 2)) (some (1, 0))
  have h11_6 : c (some (2, 2)) = c (some (1, 1)) →
      c (some (0, 0)) = c (some (2, 2)) ∧ c none = c (some (2, 2)) :=
    hc (some (2, 2)) (some (1, 1))
  have h11_7 : c (some (2, 2)) = c (some (1, 2)) →
      c (some (0, 2)) = c (some (2, 2)) ∧ c none = c (some (2, 2)) :=
    hc (some (2, 2)) (some (1, 2))
  have h11_8 : c (some (2, 2)) = c (some (1, 3)) →
      c (some (0, 0)) = c (some (2, 2)) ∧ c none = c (some (2, 2)) :=
    hc (some (2, 2)) (some (1, 3))
  have h11_9 : c (some (2, 2)) = c (some (2, 0)) →
      c (some (2, 0)) = c (some (2, 2)) ∧ c (some (2, 2)) = c (some (2, 2)) :=
    hc (some (2, 2)) (some (2, 0))
  have h11_10 : c (some (2, 2)) = c (some (2, 1)) →
      c (some (2, 0)) = c (some (2, 2)) ∧ c none = c (some (2, 2)) :=
    hc (some (2, 2)) (some (2, 1))
  have h12_0 : c (some (2, 3)) = c none →
      c (some (2, 3)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) none
  have h12_1 : c (some (2, 3)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (2, 3)) ∧ c (some (2, 3)) = c (some (2, 3)) :=
    hc (some (2, 3)) (some (0, 0))
  have h12_2 : c (some (2, 3)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) (some (0, 1))
  have h12_3 : c (some (2, 3)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) (some (0, 2))
  have h12_4 : c (some (2, 3)) = c (some (0, 3)) →
      c (some (0, 3)) = c (some (2, 3)) ∧ c (some (2, 3)) = c (some (2, 3)) :=
    hc (some (2, 3)) (some (0, 3))
  have h12_5 : c (some (2, 3)) = c (some (1, 0)) →
      c (some (0, 0)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) (some (1, 0))
  have h12_6 : c (some (2, 3)) = c (some (1, 1)) →
      c (some (0, 0)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) (some (1, 1))
  have h12_7 : c (some (2, 3)) = c (some (1, 2)) →
      c (some (0, 0)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) (some (1, 2))
  have h12_8 : c (some (2, 3)) = c (some (1, 3)) →
      c (some (0, 3)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) (some (1, 3))
  have h12_9 : c (some (2, 3)) = c (some (2, 0)) →
      c (some (2, 0)) = c (some (2, 3)) ∧ c (some (2, 3)) = c (some (2, 3)) :=
    hc (some (2, 3)) (some (2, 0))
  have h12_10 : c (some (2, 3)) = c (some (2, 1)) →
      c (some (2, 0)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) (some (2, 1))
  have h12_11 : c (some (2, 3)) = c (some (2, 2)) →
      c (some (2, 0)) = c (some (2, 3)) ∧ c none = c (some (2, 3)) :=
    hc (some (2, 3)) (some (2, 2))
  have h13_0 : c (some (3, 0)) = c none →
      c (some (3, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) none
  have h13_1 : c (some (3, 0)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c (some (3, 0)) = c (some (3, 0)) :=
    hc (some (3, 0)) (some (0, 0))
  have h13_2 : c (some (3, 0)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c (some (3, 1)) = c (some (3, 0)) :=
    hc (some (3, 0)) (some (0, 1))
  have h13_3 : c (some (3, 0)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c (some (3, 2)) = c (some (3, 0)) :=
    hc (some (3, 0)) (some (0, 2))
  have h13_4 : c (some (3, 0)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c (some (3, 3)) = c (some (3, 0)) :=
    hc (some (3, 0)) (some (0, 3))
  have h13_5 : c (some (3, 0)) = c (some (1, 0)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) (some (1, 0))
  have h13_6 : c (some (3, 0)) = c (some (1, 1)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) (some (1, 1))
  have h13_7 : c (some (3, 0)) = c (some (1, 2)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) (some (1, 2))
  have h13_8 : c (some (3, 0)) = c (some (1, 3)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) (some (1, 3))
  have h13_9 : c (some (3, 0)) = c (some (2, 0)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) (some (2, 0))
  have h13_10 : c (some (3, 0)) = c (some (2, 1)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) (some (2, 1))
  have h13_11 : c (some (3, 0)) = c (some (2, 2)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) (some (2, 2))
  have h13_12 : c (some (3, 0)) = c (some (2, 3)) →
      c (some (0, 0)) = c (some (3, 0)) ∧ c none = c (some (3, 0)) :=
    hc (some (3, 0)) (some (2, 3))
  have h14_0 : c (some (3, 1)) = c none →
      c (some (3, 1)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) none
  have h14_1 : c (some (3, 1)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c (some (3, 1)) = c (some (3, 1)) :=
    hc (some (3, 1)) (some (0, 0))
  have h14_2 : c (some (3, 1)) = c (some (0, 1)) →
      c (some (0, 1)) = c (some (3, 1)) ∧ c (some (3, 1)) = c (some (3, 1)) :=
    hc (some (3, 1)) (some (0, 1))
  have h14_3 : c (some (3, 1)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (0, 2))
  have h14_4 : c (some (3, 1)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (0, 3))
  have h14_5 : c (some (3, 1)) = c (some (1, 0)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (1, 0))
  have h14_6 : c (some (3, 1)) = c (some (1, 1)) →
      c (some (0, 1)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (1, 1))
  have h14_7 : c (some (3, 1)) = c (some (1, 2)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (1, 2))
  have h14_8 : c (some (3, 1)) = c (some (1, 3)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (1, 3))
  have h14_9 : c (some (3, 1)) = c (some (2, 0)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (2, 0))
  have h14_10 : c (some (3, 1)) = c (some (2, 1)) →
      c (some (0, 1)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (2, 1))
  have h14_11 : c (some (3, 1)) = c (some (2, 2)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (2, 2))
  have h14_12 : c (some (3, 1)) = c (some (2, 3)) →
      c (some (0, 0)) = c (some (3, 1)) ∧ c none = c (some (3, 1)) :=
    hc (some (3, 1)) (some (2, 3))
  have h14_13 : c (some (3, 1)) = c (some (3, 0)) →
      c (some (3, 0)) = c (some (3, 1)) ∧ c (some (3, 1)) = c (some (3, 1)) :=
    hc (some (3, 1)) (some (3, 0))
  have h15_0 : c (some (3, 2)) = c none →
      c (some (3, 2)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) none
  have h15_1 : c (some (3, 2)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c (some (3, 2)) = c (some (3, 2)) :=
    hc (some (3, 2)) (some (0, 0))
  have h15_2 : c (some (3, 2)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (0, 1))
  have h15_3 : c (some (3, 2)) = c (some (0, 2)) →
      c (some (0, 2)) = c (some (3, 2)) ∧ c (some (3, 2)) = c (some (3, 2)) :=
    hc (some (3, 2)) (some (0, 2))
  have h15_4 : c (some (3, 2)) = c (some (0, 3)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (0, 3))
  have h15_5 : c (some (3, 2)) = c (some (1, 0)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (1, 0))
  have h15_6 : c (some (3, 2)) = c (some (1, 1)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (1, 1))
  have h15_7 : c (some (3, 2)) = c (some (1, 2)) →
      c (some (0, 2)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (1, 2))
  have h15_8 : c (some (3, 2)) = c (some (1, 3)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (1, 3))
  have h15_9 : c (some (3, 2)) = c (some (2, 0)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (2, 0))
  have h15_10 : c (some (3, 2)) = c (some (2, 1)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (2, 1))
  have h15_11 : c (some (3, 2)) = c (some (2, 2)) →
      c (some (0, 2)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (2, 2))
  have h15_12 : c (some (3, 2)) = c (some (2, 3)) →
      c (some (0, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (2, 3))
  have h15_13 : c (some (3, 2)) = c (some (3, 0)) →
      c (some (3, 0)) = c (some (3, 2)) ∧ c (some (3, 2)) = c (some (3, 2)) :=
    hc (some (3, 2)) (some (3, 0))
  have h15_14 : c (some (3, 2)) = c (some (3, 1)) →
      c (some (3, 0)) = c (some (3, 2)) ∧ c none = c (some (3, 2)) :=
    hc (some (3, 2)) (some (3, 1))
  have h16_0 : c (some (3, 3)) = c none →
      c (some (3, 3)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) none
  have h16_1 : c (some (3, 3)) = c (some (0, 0)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c (some (3, 3)) = c (some (3, 3)) :=
    hc (some (3, 3)) (some (0, 0))
  have h16_2 : c (some (3, 3)) = c (some (0, 1)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (0, 1))
  have h16_3 : c (some (3, 3)) = c (some (0, 2)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (0, 2))
  have h16_4 : c (some (3, 3)) = c (some (0, 3)) →
      c (some (0, 3)) = c (some (3, 3)) ∧ c (some (3, 3)) = c (some (3, 3)) :=
    hc (some (3, 3)) (some (0, 3))
  have h16_5 : c (some (3, 3)) = c (some (1, 0)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (1, 0))
  have h16_6 : c (some (3, 3)) = c (some (1, 1)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (1, 1))
  have h16_7 : c (some (3, 3)) = c (some (1, 2)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (1, 2))
  have h16_8 : c (some (3, 3)) = c (some (1, 3)) →
      c (some (0, 3)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (1, 3))
  have h16_9 : c (some (3, 3)) = c (some (2, 0)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (2, 0))
  have h16_10 : c (some (3, 3)) = c (some (2, 1)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (2, 1))
  have h16_11 : c (some (3, 3)) = c (some (2, 2)) →
      c (some (0, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (2, 2))
  have h16_12 : c (some (3, 3)) = c (some (2, 3)) →
      c (some (0, 3)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (2, 3))
  have h16_13 : c (some (3, 3)) = c (some (3, 0)) →
      c (some (3, 0)) = c (some (3, 3)) ∧ c (some (3, 3)) = c (some (3, 3)) :=
    hc (some (3, 3)) (some (3, 0))
  have h16_14 : c (some (3, 3)) = c (some (3, 1)) →
      c (some (3, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (3, 1))
  have h16_15 : c (some (3, 3)) = c (some (3, 2)) →
      c (some (3, 0)) = c (some (3, 3)) ∧ c none = c (some (3, 3)) :=
    hc (some (3, 3)) (some (3, 2))
  clear hc
  have b0 : c none = false ∨ c none = true := by cases c none <;> simp
  have b1 : c (some (0, 0)) = false ∨ c (some (0, 0)) = true := by cases c (some (0, 0)) <;> simp
  have b2 : c (some (0, 1)) = false ∨ c (some (0, 1)) = true := by cases c (some (0, 1)) <;> simp
  have b3 : c (some (0, 2)) = false ∨ c (some (0, 2)) = true := by cases c (some (0, 2)) <;> simp
  have b4 : c (some (0, 3)) = false ∨ c (some (0, 3)) = true := by cases c (some (0, 3)) <;> simp
  have b5 : c (some (1, 0)) = false ∨ c (some (1, 0)) = true := by cases c (some (1, 0)) <;> simp
  have b6 : c (some (1, 1)) = false ∨ c (some (1, 1)) = true := by cases c (some (1, 1)) <;> simp
  have b7 : c (some (1, 2)) = false ∨ c (some (1, 2)) = true := by cases c (some (1, 2)) <;> simp
  have b8 : c (some (1, 3)) = false ∨ c (some (1, 3)) = true := by cases c (some (1, 3)) <;> simp
  have b9 : c (some (2, 0)) = false ∨ c (some (2, 0)) = true := by cases c (some (2, 0)) <;> simp
  have b10 : c (some (2, 1)) = false ∨ c (some (2, 1)) = true := by cases c (some (2, 1)) <;> simp
  have b11 : c (some (2, 2)) = false ∨ c (some (2, 2)) = true := by cases c (some (2, 2)) <;> simp
  have b12 : c (some (2, 3)) = false ∨ c (some (2, 3)) = true := by cases c (some (2, 3)) <;> simp
  have b13 : c (some (3, 0)) = false ∨ c (some (3, 0)) = true := by cases c (some (3, 0)) <;> simp
  have b14 : c (some (3, 1)) = false ∨ c (some (3, 1)) = true := by cases c (some (3, 1)) <;> simp
  have b15 : c (some (3, 2)) = false ∨ c (some (3, 2)) = true := by cases c (some (3, 2)) <;> simp
  have b16 : c (some (3, 3)) = false ∨ c (some (3, 3)) = true := by cases c (some (3, 3)) <;> simp
  have hall : c none = c (some (0, 0)) ∧
      c (some (0, 1)) = c (some (0, 0)) ∧
      c (some (0, 2)) = c (some (0, 0)) ∧
      c (some (0, 3)) = c (some (0, 0)) ∧
      c (some (1, 0)) = c (some (0, 0)) ∧
      c (some (1, 1)) = c (some (0, 0)) ∧
      c (some (1, 2)) = c (some (0, 0)) ∧
      c (some (1, 3)) = c (some (0, 0)) ∧
      c (some (2, 0)) = c (some (0, 0)) ∧
      c (some (2, 1)) = c (some (0, 0)) ∧
      c (some (2, 2)) = c (some (0, 0)) ∧
      c (some (2, 3)) = c (some (0, 0)) ∧
      c (some (3, 0)) = c (some (0, 0)) ∧
      c (some (3, 1)) = c (some (0, 0)) ∧
      c (some (3, 2)) = c (some (0, 0)) ∧
      c (some (3, 3)) = c (some (0, 0)) := by
    grind (splits := 64)
  rcases hall with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩
  intro a
  cases a with
  | none => exact k0
  | some a =>
    rcases a with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> first | rfl | assumption

private theorem no_partition {u v : Set (WithTop (IntervalForest 6))}
    (huv : u ∪ v = Set.range embed) (hd : Disjoint u v)
    (hnu : u.Nonempty) (hnv : v.Nonempty)
    (hcu : AmbientClosed u) (hcv : AmbientClosed v) : False := by
  classical
  let c : Code → Bool := fun a => decide (embed a ∈ u)
  have hv : ∀ a, embed a ∉ u → embed a ∈ v := by
    intro a ha
    have hmem : embed a ∈ u ∪ v := huv.symm ▸ Set.mem_range_self a
    exact hmem.resolve_left ha
  have hnotu : ∀ {x}, x ∈ v → x ∉ u := by
    intro x hx hxu
    exact Set.disjoint_left.mp hd hxu hx
  have hc : ∀ a b, c a = c b →
      c (meetCode a b) = c a ∧ c (joinCode a b) = c a := by
    intro a b hab
    by_cases ha : embed a ∈ u
    · have hb : embed b ∈ u := by simpa [c, ha] using hab.symm
      obtain ⟨⟨m, hm, hgm⟩, ⟨j, hj, hlj⟩⟩ := hcu _ ha _ hb
      have hm' : embed (meetCode a b) ∈ u := (hgm.unique (meet_extremum a b)) ▸ hm
      have hj' : embed (joinCode a b) ∈ u := (hlj.unique (join_extremum a b)) ▸ hj
      simp [c, ha, hm', hj']
    · have hb : embed b ∉ u := by simpa [c, ha] using hab.symm
      obtain ⟨⟨m, hm, hgm⟩, ⟨j, hj, hlj⟩⟩ := hcv _ (hv a ha) _ (hv b hb)
      have hm' : embed (meetCode a b) ∈ v := (hgm.unique (meet_extremum a b)) ▸ hm
      have hj' : embed (joinCode a b) ∈ v := (hlj.unique (join_extremum a b)) ▸ hj
      simp [c, ha, hnotu hm', hnotu hj']
  obtain ⟨x, hx⟩ := hnu
  obtain ⟨y, hy⟩ := hnv
  obtain ⟨a, rfl⟩ := (show x ∈ Set.range embed from huv ▸ Or.inl hx)
  obtain ⟨b, rfl⟩ := (show y ∈ Set.range embed from huv ▸ Or.inr hy)
  have hab : c a = c b := (colour_constant c hc a).trans (colour_constant c hc b).symm
  simp [c, hx, hnotu hy] at hab

private theorem witness_not_dismantlable : ¬ Dismantlable (Set.range embed) := by
  intro h
  generalize he : Set.range embed = s at h
  have hall : ∀ a, embed a ∈ s := fun a => he ▸ Set.mem_range_self a
  cases h with
  | singleton x =>
    have h0 : embed (some (0, 0)) = x := Set.mem_singleton_iff.mp (hall _)
    have ht : embed none = x := Set.mem_singleton_iff.mp (hall _)
    have he := embed_injective (h0.trans ht.symm)
    cases he
  | split _ hu hd hnu hnv hcu hcv _ _ => exact no_partition (hu.trans he.symm) hd hnu hnv hcu hcv

private theorem core_not_dismantlable :
    ¬ Dismantlable (Set.univ : Set (WithTop (IntervalForest 6))) := by
  intro h
  exact witness_not_dismantlable
    (hereditary h (Set.subset_univ _) ⟨embed none, ⟨none, rfl⟩⟩ witness_closed)

/-- The literal all-positive-size question, with disjoint sublattice subdivisions. -/
def claim : Prop := ∀ n : Nat, 1 ≤ n → Dismantlable (Set.univ : Set (Pi n))

/-- The actual priority lattice at size six refutes the universal question. -/
theorem result : ¬ claim := by
  intro h
  have hc := dismantlable_image (coreOrderIso 6) (h 6 (by omega))
  have he : coreOrderIso 6 '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective (coreOrderIso 6).surjective
  exact core_not_dismantlable (he ▸ hc)

end D5.S3.Combinatorics.PriorityLattice.SublatticeDismantling
