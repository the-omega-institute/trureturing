/- GID: D5/S3/Combinatorics/CircularWords/DisjointBlockContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/DisjointBlockContraction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   utility: none
   digest: Expansion and restriction of disjoint original-label runs on oriented circles. -/

import D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.SplitBy
import Mathlib.Data.Fintype.Perm

/-! Runs expand jointly on one oriented circle; restriction recovers their labels. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CircularWords.DisjointBlockContraction

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport

universe u v
variable {α : Type u} {β : Type v}

/-- Flattening complete original-label runs respects rotation of the marker circle. -/
private theorem flatMap_rotated (f : β → List α) {l k : List β} (h : l.IsRotated k) :
    (l.flatMap f).IsRotated (k.flatMap f) := by
  obtain ⟨n, rfl⟩ := h
  rw [List.rotate_eq_drop_append_take_mod, List.flatMap_append]
  have hh := List.isRotated_append
    (l := (l.take (n % l.length)).flatMap f)
    (l' := (l.drop (n % l.length)).flatMap f)
  simpa only [← List.flatMap_append, List.take_append_drop] using hh

/-- Expand each distinct marker by its entire ordered run, on the same oriented circle. -/
def expand (f : β → List α) : Cycle β → Cycle α :=
  Quot.map (List.flatMap f) (fun _ _ h => flatMap_rotated f h)

variable [DecidableEq α] [DecidableEq β]

/-- A prescribed original-label set is one proper circular run. -/
def Arc (A S : Finset α) (C : Cycle α) : Prop :=
  ∃ u v : List α, u.Perm S.toList ∧ v.Perm (A \ S).toList ∧
    C = (u ++ v : List α)

/-- The actual orders of a finite set, rather than an assumed factorial inventory. -/
noncomputable def orders (A : Finset α) : Finset (List α) :=
  A.toList.permutations.toFinset

/-- The actual oriented rotation quotient of those orders. -/
noncomputable def circles (A : Finset α) : Finset (Cycle α) :=
  (orders A).image Cycle.ofList

theorem mem_orders {A : Finset α} {w : List α} :
    w ∈ orders A ↔ w.Perm A.toList := by
  simp [orders, List.mem_permutations]

theorem orders_card (A : Finset α) : (orders A).card = A.card.factorial := by
  rw [orders, List.toFinset_card_of_nodup (List.nodup_permutations _ A.nodup_toList),
    List.length_permutations, Finset.length_toList]

/-- Concatenating disjoint complete original-label inventories gives an actual order. -/
theorem append_order {A S : Finset α} (hS : S ⊆ A) {l k : List α}
    (hl : l.Perm S.toList) (hk : k.Perm (A \ S).toList) : (l++k).Perm A.toList := by
  have hn : (l++k).Nodup := by
    refine List.nodup_append.mpr ⟨hl.nodup_iff.mpr S.nodup_toList,
      hk.nodup_iff.mpr (A \ S).nodup_toList, ?_⟩
    intro x hx y hy he
    subst y
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp (hk.mem_iff.mp hy))).2
      (Finset.mem_toList.mp (hl.mem_iff.mp hx))
  apply (List.perm_ext_iff_of_nodup hn A.nodup_toList).mpr
  intro x
  simp only [List.mem_append, hl.mem_iff, hk.mem_iff, Finset.mem_toList, Finset.mem_sdiff]
  exact ⟨fun h => h.elim (fun hx => hS hx) And.left,
    fun hx => (em (x ∈ S)).elim Or.inl (fun hs => Or.inr ⟨hx,hs⟩)⟩

theorem arc_complement {A S : Finset α} (hS : S ⊆ A) (C : Cycle α) :
    Arc A S C ↔ Arc A (A \ S) C := by
  have he : A \ (A \ S) = S := Finset.sdiff_sdiff_eq_self hS
  constructor <;> rintro ⟨u,v,hu,hv,hC⟩
  · refine ⟨v,u,hv,?_,?_⟩
    · simpa [he] using hu
    · rw [hC]
      exact Cycle.coe_eq_coe.mpr List.isRotated_append
  · refine ⟨v,u,?_,hu,?_⟩
    · simpa [he] using hv
    · rw [hC]
      exact Cycle.coe_eq_coe.mpr List.isRotated_append

/-- Filtering an expanded word recovers exactly the selected original-label fibers. -/
theorem restrict_expand (f : β → List α) (p : α → Bool) (C : Cycle β) :
    restrict p (expand f C) = expand (fun b => (f b).filter p) C := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change (((l.flatMap f).filter p : List α) : Cycle α) = _
    rw [List.filter_flatMap]
    rfl

/-- A proper run has one incoming boundary, even before imposing distinct labels. -/
theorem boundary_root_unique (P : α → Prop) {u v u' v' : List α}
    (hu0 : u ≠ []) (hv0 : v ≠ []) (hu0' : u' ≠ []) (hv0' : v' ≠ [])
    (hu : ∀ x ∈ u, P x) (hv : ∀ x ∈ v, ¬ P x)
    (hu' : ∀ x ∈ u', P x) (hv' : ∀ x ∈ v', ¬ P x)
    (hc : (u ++ v : List α) = (u' ++ v' : Cycle α)) :
    u ++ v = u' ++ v' := by
  obtain ⟨d, hd, hr⟩ := List.isRotated_iff_mod.mp (Cycle.coe_eq_coe.mp hc)
  by_cases hz : d = 0
  · simpa [hz] using hr
  by_cases he : d = (u ++ v).length
  · simpa only [he, List.rotate_length] using hr
  have hdlt : d < (u ++ v).length := by omega
  have hstart : P ((u ++ v)[d]'hdlt) := by
    have hh := congrArg List.head? hr
    rw [List.head?_rotate hdlt, List.getElem?_eq_getElem hdlt,
      List.head?_append, List.head?_eq_some_head hu0'] at hh
    simp only [Option.some_or, Option.some.injEq] at hh
    rw [hh]
    exact hu' _ (List.head_mem hu0')
  have hdu : d < u.length := by
    by_contra hn
    have hdge : u.length ≤ d := Nat.le_of_not_gt hn
    rw [List.getElem_append_right hdge] at hstart
    exact hv _ (List.mem_of_getElem rfl) hstart
  have ht0 : u.take d ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    rw [List.length_take, List.length_nil, Nat.min_eq_left hdu.le] at hlen
    exact hz hlen
  have ht : (u ++ v).take d = u.take d := by
    simp [List.take_append, Nat.sub_eq_zero_of_le hdu.le]
  have hh := congrArg List.getLast? hr
  rw [List.rotate_eq_drop_append_take hdlt.le, List.getLast?_append,
    ht, List.getLast?_eq_some_getLast ht0] at hh
  have hnv : u' ++ v' ≠ [] := List.append_ne_nil_of_right_ne_nil _ hv0'
  rw [List.getLast?_eq_some_getLast hnv] at hh
  simp only [Option.some_or, Option.some.injEq] at hh
  have hp : P ((u' ++ v').getLast hnv) := by
    rw [← hh]
    exact hu _ (List.mem_of_mem_take (List.getLast_mem ht0))
  rw [List.getLast_append_right hv0'] at hp
  exact False.elim (hv' _ (List.getLast_mem hv0') hp)

/-- The two original internal orders are recovered from a proper circular two-block division. -/
theorem two_block_injective {A S : Finset α} (hS : S ⊆ A)
    (hs0 : S.Nonempty) (hv0 : (A \ S).Nonempty)
    {u v u' v' : List α}
    (hu : u.Perm S.toList) (hv : v.Perm (A \ S).toList)
    (hu' : u'.Perm S.toList) (hv' : v'.Perm (A \ S).toList)
    (hc : (u ++ v : List α) = (u' ++ v' : Cycle α)) : u = u' ∧ v = v' := by
  have hroot : u ++ v = u' ++ v' := boundary_root_unique (fun x => x ∈ S)
    (by simpa only [← List.length_pos_iff, hu.length_eq, Finset.length_toList] using hs0.card_pos)
    (by simpa only [← List.length_pos_iff, hv.length_eq, Finset.length_toList] using hv0.card_pos)
    (by simpa only [← List.length_pos_iff, hu'.length_eq, Finset.length_toList] using hs0.card_pos)
    (by simpa only [← List.length_pos_iff, hv'.length_eq, Finset.length_toList] using hv0.card_pos)
    (fun x hx => Finset.mem_toList.mp (hu.mem_iff.mp hx))
    (fun x hx => (Finset.mem_sdiff.mp (Finset.mem_toList.mp (hv.mem_iff.mp hx))).2)
    (fun x hx => Finset.mem_toList.mp (hu'.mem_iff.mp hx))
    (fun x hx => (Finset.mem_sdiff.mp (Finset.mem_toList.mp (hv'.mem_iff.mp hx))).2) hc
  have hul : u.length = u'.length := hu.length_eq.trans hu'.length_eq.symm
  exact List.append_inj hroot hul

/-- Cut at the unique incoming boundary of a prescribed proper run.
The inverse expands both original internal lists into the same oriented circle. -/
noncomputable def twoBlockEquiv (A S : Finset α) (hS : S ⊆ A)
    (hs0 : S.Nonempty) (hv0 : (A \ S).Nonempty) :
    ({u : List α // u ∈ orders S} × {v : List α // v ∈ orders (A \ S)}) ≃
      {C : Cycle α // Arc A S C} := by
  let F : ({u : List α // u ∈ orders S} × {v : List α // v ∈ orders (A \ S)}) →
      {C : Cycle α // Arc A S C} := fun z =>
    ⟨(z.1.val ++ z.2.val : List α), z.1.val, z.2.val,
      mem_orders.mp z.1.property, mem_orders.mp z.2.property, rfl⟩
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨u,v⟩ ⟨u',v'⟩ h
    have he := two_block_injective hS hs0 hv0
      (mem_orders.mp u.property) (mem_orders.mp v.property)
      (mem_orders.mp u'.property) (mem_orders.mp v'.property)
      (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2)
  · rintro ⟨C,u,v,hu,hv,hC⟩
    refine ⟨(⟨u,mem_orders.mpr hu⟩,⟨v,mem_orders.mpr hv⟩), ?_⟩
    exact Subtype.ext hC.symm

/-- Exact single-arc multiplicity, obtained from the boundary contraction equivalence. -/
theorem arc_card (A S : Finset α) (hS : S ⊆ A)
    (hs0 : S.Nonempty) (hv0 : (A \ S).Nonempty) :
    Nat.card {C : Cycle α // Arc A S C} = S.card.factorial * (A \ S).card.factorial := by
  have he := Nat.card_congr (twoBlockEquiv A S hS hs0 hv0)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe, orders_card]
    using he.symm

end D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
