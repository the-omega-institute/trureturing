/- GID: D5/S3/Combinatorics/CircularWords/CircularDeletionTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/CircularDeletionTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   utility: none
   digest: Negative oriented deletion transport omits all but at most two initial labels. -/

import Mathlib.Data.List.Cycle
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.CircularDeletionTransport

universe u
variable {α : Type u}

/-- Filtering descends through the existing rotation quotient. -/
private theorem filter_rotated (p : α → Bool) {l r : List α} (h : l ~r r) :
    l.filter p ~r r.filter p := by
  obtain ⟨k, rfl⟩ := h
  rw [List.rotate_eq_drop_append_take_mod, List.filter_append]
  have e := List.isRotated_append
    (l := (l.take (k % l.length)).filter p)
    (l' := (l.drop (k % l.length)).filter p)
  simpa only [← List.filter_append, List.take_append_drop] using e

/-- Restriction of a genuine oriented circular word to selected labels. -/
def restrict (p : α → Bool) : Cycle α → Cycle α :=
  Quot.map (fun l => l.filter p) (fun _ _ h => filter_rotated p h)

theorem restrict_reverse (p : α → Bool) (C : Cycle α) :
    restrict p C.reverse = (restrict p C).reverse := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change ((l.reverse.filter p : List α) : Cycle α) = ((l.filter p).reverse : List α)
    rw [List.filter_reverse]

theorem restrict_restrict (p q : α → Bool) (C : Cycle α) :
    restrict p (restrict q C) = restrict (fun y => p y && q y) C := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change ((List.filter p (List.filter q l) : List α) : Cycle α) =
      (List.filter (fun y => p y && q y) l : Cycle α)
    rw [List.filter_filter]

variable [DecidableEq α]

/-- The oriented residual of the actual complete supplier omitting x. -/
def delete (x : α) : Cycle α → Cycle α := restrict (fun y => decide (y ≠ x))

private theorem restrict_delete (p : α → Bool) (x : α) (hx : p x = false) (C : Cycle α) :
    restrict p (delete x C) = restrict p C := by
  rw [delete, restrict_restrict]
  have e : (fun y => p y && decide (y ≠ x)) = p := by
    funext y
    by_cases h : y = x
    · subst y; simp [hx]
    · simp [h]
  rw [e]

/-- A walk through actual oriented deletion/reinsertion incidences. -/
inductive DeleteWalk : List α → Cycle α → Cycle α → Prop where
  | nil (C : Cycle α) : DeleteWalk [] C C
  | cons {x : α} {xs : List α} {C D E : Cycle α}
      (step : delete x C = delete x D) (tail : DeleteWalk xs D E) :
      DeleteWalk (x :: xs) C E

/-- Actual deletion steps preserve every circular restriction of untouched labels. -/
theorem restrict_walk {xs : List α} {C D : Cycle α} (h : DeleteWalk xs C D)
    (p : α → Bool) (untouched : ∀ x ∈ xs, p x = false) :
    restrict p C = restrict p D := by
  induction h with
  | nil C => rfl
  | @cons x xs C D E step tail ih =>
    have hx := untouched x (by simp)
    have ht : ∀ y ∈ xs, p y = false := fun y hy => untouched y (by simp [hy])
    calc
      restrict p C = restrict p (delete x C) := (restrict_delete p x hx C).symm
      _ = restrict p (delete x D) := congrArg (restrict p) step
      _ = restrict p D := restrict_delete p x hx D
      _ = restrict p E := ih ht

/-- Every ordering of three distinct labels has one of the two genuine circular orders. -/
private theorem triple_orientations {a b c : α} {l : List α} (hp : l.Perm [a,b,c]) :
    (l : Cycle α) = ([a,b,c] : List α) ∨ (l : Cycle α) = ([a,c,b] : List α) := by
  have ha : a ∈ l := hp.mem_iff.mpr (by simp)
  have hh : (l.rotate (l.idxOf a)).head? = some a := by
    rw [List.head?_rotate (List.idxOf_lt_length_iff.mpr ha)]
    exact List.getElem?_idxOf ha
  have hr : (l : Cycle α) = (l.rotate (l.idxOf a) : List α) :=
    Cycle.coe_eq_coe.mpr ⟨l.idxOf a, rfl⟩
  have hpr : (l.rotate (l.idxOf a)).Perm [a,b,c] := (List.rotate_perm l _).trans hp
  cases e : l.rotate (l.idxOf a) with
  | nil => simp [e] at hh
  | cons d tail =>
    have hd : d = a := by simpa [e] using hh
    subst d
    rw [e] at hpr hr
    have ht : tail.Perm [b,c] := hpr.cons_inv
    rcases List.perm_pair.mp ht with h | h
    · left; simpa [h] using hr
    · right; simpa [h] using hr

omit [DecidableEq α] in
/-- A three-label oriented circular word has no reversal fixed point. -/
private theorem triple_cycle_not_reverse (a b c : α) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    ([a,b,c] : Cycle α) ≠ ([a,b,c] : Cycle α).reverse := by
  intro h
  rw [Cycle.reverse_coe] at h
  have hr : [a,b,c] ~r [c,b,a] := Cycle.coe_eq_coe.mp h
  obtain ⟨k,hk,he⟩ := List.isRotated_iff_mod.mp hr
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k <;> simp_all [List.rotate_cons_succ]

/-- Restriction to the actual three selected labels. -/
private def triple (a b c : α) (y : α) : Bool := decide (y = a ∨ y = b ∨ y = c)

/-- Distinct labels present in a nodup circle cannot have reversal-invariant restriction. -/
private theorem restrict_triple_not_reverse (a b c : α) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (C : Cycle α) (hn : C.Nodup)
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) :
    restrict (triple a b c) C ≠ (restrict (triple a b c) C).reverse := by
  induction C using Quotient.inductionOn with
  | _ l =>
    have hnl : l.Nodup := Cycle.nodup_coe_iff.mp hn
    have hal : a ∈ l := Cycle.mem_coe_iff.mp ha
    have hbl : b ∈ l := Cycle.mem_coe_iff.mp hb
    have hcl : c ∈ l := Cycle.mem_coe_iff.mp hc
    have hnt : ([a,b,c] : List α).Nodup := by simp [hab,hac,hbc]
    have hp : (l.filter (triple a b c)).Perm [a,b,c] := by
      apply (List.perm_ext_iff_of_nodup (hnl.filter _) hnt).mpr
      intro y
      constructor
      · intro hy
        have hy' := (List.mem_filter.mp hy).2
        simpa [triple] using hy'
      · intro hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · simp [triple,hal]
        · simp [triple,hbl]
        · simp [triple,hcl]
    change (l.filter (triple a b c) : Cycle α) ≠
      (l.filter (triple a b c) : Cycle α).reverse
    rcases triple_orientations hp with h | h
    · rw [h]; exact triple_cycle_not_reverse a b c hab hac hbc
    · rw [h]; exact triple_cycle_not_reverse a c b hac hab hbc.symm

/-- Actual negative deletion transport cannot leave three distinct labels untouched. -/
private theorem untouched_three_not_negative {xs : List α} {C D : Cycle α}
    (walk : DeleteWalk xs C D) (hn : C.Nodup)
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (ua : a ∉ xs) (ub : b ∉ xs) (uc : c ∉ xs) : D ≠ C.reverse := by
  intro end_negative
  have untouched : ∀ x ∈ xs, triple a b c x = false := by
    intro x hx
    have xa : x ≠ a := fun e => ua (e ▸ hx)
    have xb : x ≠ b := fun e => ub (e ▸ hx)
    have xc : x ≠ c := fun e => uc (e ▸ hx)
    simp [triple,xa,xb,xc]
  have preserved := restrict_walk walk (triple a b c) untouched
  rw [end_negative,restrict_reverse] at preserved
  exact restrict_triple_not_reverse a b c hab hac hbc C hn ha hb hc preserved

private theorem mem_support (C : Cycle α) (x : α) : x ∈ C.toFinset ↔ x ∈ C := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change x ∈ l.toFinset ↔ x ∈ l
    exact List.mem_toFinset

/-- Negative actual deletion transport uses all but at most two original labels. -/
theorem negative_walk_support_bound {xs : List α} {C : Cycle α}
    (walk : DeleteWalk xs C C.reverse) (hn : C.Nodup) :
    C.toFinset.card ≤ xs.toFinset.card + 2 := by
  by_contra h
  let untouched : Finset α := C.toFinset \ xs.toFinset
  have hcard : C.toFinset.card ≤ untouched.card + xs.toFinset.card := by
    calc
      C.toFinset.card ≤ (untouched ∪ xs.toFinset).card := by
        apply Finset.card_le_card
        intro x hx
        by_cases hu : x ∈ xs.toFinset
        · exact Finset.mem_union.mpr (Or.inr hu)
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx,hu⟩))
      _ ≤ untouched.card + xs.toFinset.card := Finset.card_union_le _ _
  have hthree : 2 < untouched.card := by omega
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp hthree
  have has := Finset.mem_sdiff.mp ha
  have hbs := Finset.mem_sdiff.mp hb
  have hcs := Finset.mem_sdiff.mp hc
  have ua : a ∉ xs := by simpa using has.2
  have ub : b ∉ xs := by simpa using hbs.2
  have uc : c ∉ xs := by simpa using hcs.2
  exact untouched_three_not_negative walk hn a b c hab hac hbc
    ((mem_support C a).mp has.1) ((mem_support C b).mp hbs.1)
    ((mem_support C c).mp hcs.1) ua ub uc rfl

#print axioms restrict_walk
#print axioms negative_walk_support_bound

end D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
