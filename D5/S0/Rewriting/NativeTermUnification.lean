/- GID: D5/S0/Rewriting/NativeTermUnification
   generality: G
   mirror-B: D5/B/S0/Rewriting/NativeTermUnification
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original finite unification algorithm and native fragment preservation. -/

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import D5.S0.Rewriting.NativeSubstitution
import Std.Tactic.BVDecide.Normalize.BitVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

section
set_option autoImplicit true
set_option relaxedAutoImplicit true
open List
namespace List
theorem mem_dedup_of_mem {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l.uniq → a ∈ l := by
  induction l with
  | nil => simp [uniq]
  | cons b bs ih =>
    simp [uniq]
    split
    · intro h
      exact Or.symm (Or.intro_left (a = b) (ih h))
    · intro h
      cases h with
      | head => exact Or.symm (Or.inr rfl)
      | tail _ h' => exact Or.symm (Or.intro_left (a = b) (ih h'))
theorem mem_of_mem_dedup {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l → a ∈ l.uniq := by
  induction l with
  | nil => simp [uniq]
  | cons b bs ih =>
    simp [uniq]
    intro h; cases h
    · subst a
      by_cases b ∈ bs.uniq <;> simp_all
    · by_cases b ∈ bs.uniq <;> simp_all
theorem mem_of_dedup {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l ↔ a ∈ l.uniq := by
  apply Iff.intro
  exact fun h => mem_of_mem_dedup l a h
  exact fun h => mem_dedup_of_mem l a h
theorem length_dedup_cons_of_mem {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∈ l) : (a :: l).uniq.length = l.uniq.length := by
  simp [uniq]
  have : a ∈ l.uniq := mem_of_mem_dedup l a h
  simp [this]
theorem length_dedup_cons_of_not_mem {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∉ l) : (a :: l).uniq.length = 1 + l.uniq.length := by
  induction l
  · simp_all [uniq]
  · rename_i head tail ih
    simp_all [uniq]
    obtain ⟨h1, h2⟩ := h
    split
    · have := @mem_dedup_of_mem _ _ tail a
      simp_all
      all_goals omega
    · have := @mem_dedup_of_mem _ _ tail a
      simp_all
      all_goals omega
theorem removeAll_of_cons {α : Type} [DecidableEq α] (x : α) (xs ys : List α)
  (h : x ∉ ys) :
  ((x :: xs).removeAll ys) = x :: (xs.removeAll ys) := by
  induction xs
  case nil => simp_all [removeAll]
  case cons a as ih =>
    simp_all [removeAll]
theorem length_dedup_of_removeAll {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∈ l) :
  l.uniq.length = 1 + (l.removeAll [a]).uniq.length := by
  induction l
  case nil => simp_all
  case cons x xs ih =>
    simp [uniq]
    simp at h
    by_cases h : a = x
    case pos =>
      subst a
      split
      · rename_i h_x_xs
        have : x ∈ xs := by exact (mem_of_dedup xs x).mpr h_x_xs
        have ih' := ih this
        simp_all [removeAll]
      · simp [removeAll]
        have : x ∉ xs := by
          have := @mem_of_dedup _ _ xs x
          simp_all
        have : (filter (fun x_1 => !decide (x_1 = x)) xs) = xs := by
          simp_all
          intro a ha
          exact ne_of_mem_of_not_mem ha this
        rw [this]
        all_goals omega
    case neg =>
      rename_i h_a_x_xs
      simp_all
      split
      · rename_i hx
        have := @removeAll_of_cons _ _ x xs [a]
        have h' : ¬x = a := by exact fun a_1 => h (id (Eq.symm a_1))
        simp [h'] at this
        rw [this]
        have := @length_dedup_cons_of_mem _ _ x (xs.removeAll [a])
        have : x ∈ xs.removeAll [a] := by
          simp [removeAll, h']
          exact (mem_of_dedup xs x).mpr hx
        simp_all
      · rename_i h_x_not_in_xs
        simp_all
        have := @removeAll_of_cons _ _ x xs [a]
        have h' : ¬x = a := by exact fun a_1 => h (id (Eq.symm a_1))
        simp [h'] at this
        rw [this]
        have := @length_dedup_cons_of_not_mem _ _ x (xs.removeAll [a])
        have : ¬ x ∈ xs.removeAll [a] := by
          simp [removeAll]
          have : x ∉ xs := by
            have := @mem_of_dedup _ _ xs x
            simp_all
          simp_all
        simp_all
        all_goals omega
theorem length_dedup_append_le_left {α : Type} [DecidableEq α] (l₁ l₂ : List α) :
  l₁.uniq.length ≤ (l₁ ++ l₂).uniq.length := by
  induction l₁ generalizing l₂
  case nil => simp [uniq]
  case cons a as ih =>
    simp [uniq]
    split
    · rename_i h
      have : a ∈ as := by exact (mem_of_dedup as a).mpr h
      have : a ∈ (as ++ l₂).uniq := by
        have : a ∈ as ++ l₂ := by simp_all
        exact (mem_of_dedup (as ++ l₂) a).mp this
      simp_all
    · by_cases ha : a ∈ (as ++ l₂).uniq
      case pos =>
        rename_i h_a_as
        simp_all
        have h_l2 : ∃ l, l = l₂.removeAll [a] := by simp_all
        obtain ⟨l, hl⟩ := h_l2
        simp_all
        have h_a_as_l2 : a ∈ as ++ l₂ := by exact (mem_of_dedup (as ++ l₂) a).mpr ha
        have h := @length_dedup_of_removeAll _ _ a (as ++ l₂) h_a_as_l2
        rw [h]
        have : ((as ++ l₂).removeAll [a]) = as ++ l := by
          simp [removeAll]
          have h_not_in_a_as : a ∉ as := by
            have := @mem_of_dedup _ _ as a
            simp_all
          have h_a_as : filter (fun x => !decide (x = a)) as = as := by
            simp_all
            intro a1 ha1
            exact ne_of_mem_of_not_mem ha1 h_not_in_a_as
          have h_a_l2 : filter (fun x => !decide (x = a)) l₂ = l := by
            rw [hl]
            simp [removeAll]
          simp_all
        rw [this]
        exact Nat.sub_le_iff_le_add'.mp (ih l)
      case neg =>
        simp_all
theorem length_dedup_append_all_in_right {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁.all (fun e => e ∈ l₂)) :
  (l₁ ++ l₂).uniq.length = l₂.uniq.length := by
  induction l₁
  · simp_all
  · rename_i head tail ih
    simp_all
    obtain ⟨h1, h2⟩ := h
    have h1' : head ∈ tail ++ l₂ := by simp_all
    simp [@length_dedup_cons_of_mem _ _ head (tail ++ l₂) h1']
    induction tail <;> try simp
    rename_i x xrest ih
    simp_all [uniq]
    have : x ∈ (xrest ++ l₂) := by simp_all
    have : x ∈ (xrest ++ l₂).uniq := by
      exact @mem_of_mem_dedup _ _ (xrest ++ l₂) x (by assumption)
    simp_all
    done
theorem length_dedup_append_subset_right {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁ ⊆ l₂) :
  (l₁ ++ l₂).uniq.length = l₂.uniq.length := by
  exact @length_dedup_append_all_in_right _ _ l₁ l₂ (by grind)
theorem length_dedup_append_all_in_left {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₂.all (fun e => e ∈ l₁)) :
  (l₁ ++ l₂).uniq.length = l₁.uniq.length := by
  induction l₂ generalizing l₁
  case nil => simp_all
  case cons x xs ih =>
    have h1 : (l₁ ++ x :: xs) = (l₁ ++ [x]) ++ xs := by exact append_cons l₁ x xs
    rw [h1]
    have ih' := ih (l₁ ++ [x])
    simp_all
    obtain ⟨hx, h_x_l1⟩ := h
    have h_1 := @length_dedup_of_removeAll _ _ x (l₁ ++ [x]) (by simp_all)
    have h_2 := @length_dedup_of_removeAll _ _ x (l₁) (by simp_all)
    have h_3 : ((l₁ ++ [x]).removeAll [x]) = l₁.removeAll [x] := by
      simp [removeAll]
    simp_all
theorem length_dedup_all_in_eq {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h1 : l₁.all (fun e => e ∈ l₂))
  (h2 : l₂.all (fun e => e ∈ l₁)) :
  l₁.uniq.length = l₂.uniq.length := by
  have h_1 := @length_dedup_append_all_in_right _ _ l₁ l₂ h1
  have h_2 := @length_dedup_append_all_in_left _ _ l₁ l₂ h2
  simp_all
theorem length_dedup_subset_eq {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h1 : l₁ ⊆ l₂) (h2 : l₂ ⊆ l₁) :
  l₁.uniq.length = l₂.uniq.length := by
  have := @length_dedup_all_in_eq _ _ l₁ l₂
  grind
theorem length_dedup_of_all_in_not_mem_lt {α : Type} [DecidableEq α] (l₁ l₂ : List α) (a : α)
  (h1 : l₁.all (fun e => e ∈ l₂)) (h2 : a ∉ l₁) (h3 : a ∈ l₂) :
  l₁.uniq.length < l₂.uniq.length := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp_all [uniq]
    have : a ∈ l₂.uniq := by
      have := @mem_of_dedup _ _ l₂ a
      simp_all
    exact length_pos_of_mem this
  | cons head tail ih =>
    simp at h1 ih
    simp [uniq]
    obtain ⟨h1_head_l2, h1⟩ := h1
    split
    · rename_i h_head_tail
      exact @ih l₂ h1 (by simp_all) h3
    · rename_i h_head_not_in_tail
      have h_head_tail := @length_dedup_cons_of_not_mem _ _ head tail
      by_cases h_head_in_tail : head ∈ tail
      case pos =>
        simp_all [@mem_of_dedup _ _ tail head]
      case neg =>
        have h_removeAll := @length_dedup_of_removeAll _ _ head l₂ h1_head_l2
        simp_all
        obtain ⟨h_a_head, h_a_tail⟩ := h2
        have h1' : ∀ (x : α), x ∈ tail → x ∈ l₂.removeAll [head] := by
          intro x hx
          have h_x_not_head : ¬ x = head := by exact ne_of_mem_of_not_mem hx h_head_in_tail
          have h_x_in_l2 := @h1 x hx
          simp_all [removeAll]
        have h_a_l2 : a ∈ l₂.removeAll [head] := by
          simp_all [removeAll]
        have ih' := @ih (l₂.removeAll [head]) h1' h_a_l2
        all_goals omega
  done
theorem length_dedup_of_subset_not_mem_lt {α : Type} [DecidableEq α] (l₁ l₂ : List α) (a : α)
  (h1 : l₁ ⊆ l₂) (h2 : a ∉ l₁) (h3 : a ∈ l₂) :
  l₁.uniq.length < l₂.uniq.length := by
  have := @length_dedup_of_all_in_not_mem_lt _ _ l₁ l₂ a
  grind
theorem length_dedup_of_subset_le {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁ ⊆ l₂) : l₁.uniq.length ≤ l₂.uniq.length := by
  induction l₁ with
  | nil => simp_all [uniq]
  | cons head tail ih =>
    have h_tail_l2 : tail ⊆ l₂ := by simp_all
    have ih' := @ih h_tail_l2
    by_cases h_head : head ∈ tail
    case pos =>
      have := @length_dedup_cons_of_mem _ _ head tail h_head
      exact le_of_eq_of_le this (ih h_tail_l2)
    case neg =>
      simp_all
      have := @length_dedup_of_subset_not_mem_lt _ _ tail l₂ head h_tail_l2 h_head h
      have h_head_dedup : head ∉ tail.uniq := by
        have := @mem_of_dedup _ _ tail head
        simp_all
      simp_all [uniq]
      all_goals omega
end List
end

namespace Lambda
section
set_option autoImplicit true
set_option relaxedAutoImplicit true
open Strata.Util (HMap HMaps)
abbrev Constraint := (LMonoTy × LMonoTy)
abbrev Constraints := List Constraint
def Constraint.freeVars (c : Constraint) : List TyIdentifier :=
  let (t1, t2) := c
  LMonoTy.freeVars t1 ++ LMonoTy.freeVars t2
def Constraints.freeVars (cs : Constraints) : List TyIdentifier :=
  match cs with
  | [] => []
  | c :: c_rest =>
    c.freeVars ++ Constraints.freeVars c_rest
theorem Constraints.freeVars_single_constraint_comm_subset :
    Constraints.freeVars [(t1, t2)] ⊆ Constraints.freeVars [(t2, t1)] := by
  simp [Constraints.freeVars, Constraint.freeVars]
@[simp]
theorem Constraints.freeVars_of_cons_zip :
    Constraints.freeVars ((a :: as).zip (b :: bs)) =
    LMonoTy.freeVars a ++ LMonoTy.freeVars b ++ Constraints.freeVars (as.zip bs) := by
  simp [Constraints.freeVars, Constraint.freeVars]
theorem Constraints.freeVars_of_zip_subset :
    (Constraints.freeVars (args1.zip args2)) ⊆
    (LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2) := by
  induction args1 generalizing args2 with
  | nil => simp_all [freeVars]
  | cons head tail ih =>
    unfold List.zip List.zipWith
    split
    · rename_i xs ys xs' y ys' heq
      simp_all [freeVars]
      obtain ⟨heq1, heq2⟩ := heq
      subst ys xs'
      apply And.intro
      · simp [Constraint.freeVars, Constraint.freeVars]
        simp_all (config := {maxDischargeDepth := 10})
      · have ih' := @ih ys'
        unfold List.zip at ih'
        apply List.subset_append_of_subset_right head.freeVars
        generalize LMonoTys.freeVars tail = A at *
        generalize y.freeVars = B at *
        generalize LMonoTys.freeVars ys' = C at *
        have : A ++ C ⊆ A ++ (B ++ C) := by simp_all
        exact fun _ x => this (ih' x)
    · simp_all [freeVars]
  done
theorem Constraints.freeVars_of_zip_superset (h : args1.length = args2.length) :
    (LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2) ⊆
    (Constraints.freeVars (args1.zip args2)) := by
  induction args1 generalizing args2 with
  | nil =>
    simp_all [freeVars, LMonoTys.freeVars]
    have : args2 = [] := by exact List.length_eq_zero_iff.mp (id (Eq.symm h))
    simp_all [LMonoTys.freeVars]
  | cons head tail ih =>
    cases args2
    case cons.nil =>
      simp_all
    case cons.cons x xs =>
      have ih' := @ih xs (by simp_all)
      simp only [LMonoTys.freeVars_of_cons, Constraints.freeVars_of_cons_zip]
      simp_all (config := {maxDischargeDepth := 10})
    done
def Constraint.size (c : Constraint) : Nat :=
  c.fst.size + c.snd.size
def Constraints.size (cs : Constraints) : Nat :=
  match cs with
  | [] => 0
  | c :: rest => c.size + Constraints.size rest
@[simp]
theorem Constraints.size_cons :
    Constraints.size rest < Constraints.size (c :: rest) := by
  simp [Constraints.size, Constraint.size]
  have := @LMonoTy.size_gt_zero c.fst
  have := @LMonoTy.size_gt_zero c.snd
  omega
theorem Constraints.size_zip_eq (h : args1.length = args2.length) :
    Constraints.size (args1.zip args2) = LMonoTys.size args1 + LMonoTys.size args2 := by
  induction args1 generalizing args2
  case nil =>
    simp_all [size, LMonoTys.size]
    have : args2 = [] := by exact List.length_eq_zero_iff.mp (id (Eq.symm h))
    simp_all [LMonoTys.size]
  case cons head tail ih =>
    cases args2
    case nil => simp_all
    case cons x xs =>
      simp_all [size, Constraint.size, LMonoTys.size]
      omega
def Subst.freeVars_subset_prop (cs : Constraints) (newS oldS : SubstInfo) : Prop :=
  Subst.freeVars newS.subst ⊆
  Constraints.freeVars cs ++ Subst.freeVars oldS.subst
structure ValidSubstRelation (cs : Constraints) (oldS : SubstInfo) where
  newS : SubstInfo
  goodSubset : Subst.freeVars_subset_prop cs newS oldS
@[simp]
theorem Subst.freeVars_subset_prop_of_empty (S : SubstInfo) :
    Subst.freeVars_subset_prop [] S S := by
  simp [Subst.freeVars_subset_prop]
theorem Subst.freeVars_subset_prop_single_constraint_comm :
    Subst.freeVars_subset_prop [(t1, t2)] newS oldS =
    Subst.freeVars_subset_prop [(t2, t1)] newS oldS := by
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars]
  apply propext
  constructor
  · intro h x hx
    have hmem := h hx
    simp only [List.append_assoc, List.nil_append, List.mem_append] at hmem ⊢
    rcases hmem with h1 | h2 | h3
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h2
    · exact Or.inr (Or.inr h3)
  · intro h x hx
    have hmem := h hx
    simp only [List.append_assoc, List.nil_append, List.mem_append] at hmem ⊢
    rcases hmem with h1 | h2 | h3
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h2
    · exact Or.inr (Or.inr h3)
private theorem Subst.freeVars_subset_prop_mk_cons
    (R1 : ValidSubstRelation [c] S)
    (R2 : ValidSubstRelation c_rest R1.newS) :
    Subst.freeVars_subset_prop (c :: c_rest) R2.newS S := by
  obtain ⟨h_si_1, h_prop_1⟩ := R1
  obtain ⟨h_si_2, h_prop_2⟩ := R2
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars,
    List.append_assoc, List.nil_append] at h_prop_1 h_prop_2 ⊢
  intro x hx
  have hB := h_prop_2 hx
  rcases List.mem_append.mp hB with h | h
  · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ h))
  · have hA := h_prop_1 h
    rcases List.mem_append.mp hA with h' | h'
    · exact List.mem_append_left _ h'
    · rcases List.mem_append.mp h' with h'' | h''
      · exact List.mem_append_right _ (List.mem_append_left _ h'')
      · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h''))
private theorem ugly_subset_lemma {α : Type} [DecidableEq α]
    (newS oldS sty lty orig_lty : List α)
    (h1 : newS ⊆ sty ++ (lty ++ oldS))
    (h2 : sty ⊆ oldS)
    (h3 : lty ⊆ orig_lty ++ oldS) :
    newS ⊆ orig_lty ++ oldS := by
  have h1' : newS ⊆ sty ++ lty ++ oldS := by simp_all
  clear h1
  have h2 : sty ++ lty ++ oldS ⊆ (lty ++ oldS) := by simp_all
  have h3 : newS ⊆ (lty ++ oldS) := fun _ a_1 => h2 (h1' a_1)
  have h4 : lty ++ oldS ⊆ orig_lty ++ oldS := by simp_all
  exact fun _ a_1 => h4 (h3 a_1)
theorem Subst.freeVars_subset_prop_of_ftvar_id_when_id_in_S
    (S : SubstInfo) (id : TyIdentifier) (orig_lty sty lty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : HMaps.find? S.subst id = some sty)
    (relS : ValidSubstRelation [(sty, lty)] S) :
    Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] relS.newS S := by
  obtain ⟨newS, h_newS_subset⟩ := relS
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars,
    LMonoTy.freeVars, List.append_assoc, List.nil_append] at h_newS_subset ⊢
  have h_sty := Subst.freeVars_of_find_subset S.subst _h5
  have h_lty_sub := LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  apply List.subset_append_of_subset_right
  have key := ugly_subset_lemma (Subst.freeVars newS.subst) (Subst.freeVars S.subst)
    sty.freeVars lty.freeVars orig_lty.freeVars
  apply key
  · intro x hx
    have := h_newS_subset hx
    simpa [List.append_assoc] using this
  · exact h_sty
  · rw [h_lty]; exact h_lty_sub
theorem Subst.freeVars_subset_prop_of_single_constraint
    (S newS : SubstInfo) (new_subst : Subst) (id : TyIdentifier) (orig_lty lty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (h_new_subst : new_subst = HMaps.insert (Subst.apply (HMap.single id lty) S.subst) id lty)
    (h' : SubstWF new_subst)
    (h_newS : newS = { subst := new_subst, isWF := h' }) :
    Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] newS S := by
  subst h_newS h_new_subst h_lty
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars,
    LMonoTy.freeVars, List.append_assoc, List.nil_append]
  have h_ins := Subst.freeVars_of_insert
    (Subst.apply (HMap.single id (LMonoTy.subst S.subst orig_lty)) S.subst)
    id (LMonoTy.subst S.subst orig_lty)
  have h_apply := Subst.freeVars_of_apply_subset_alt
    (HMap.single id (LMonoTy.subst S.subst orig_lty)) S.subst
  have h_orig := LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  have h_single := Subst.freeVars_singleton_subset id (LMonoTy.subst S.subst orig_lty)
  simp only [Subst.singleton] at h_single
  intro x hx
  suffices hsuff : x ∈ orig_lty.freeVars ++ Subst.freeVars S.subst by
    exact List.mem_cons_of_mem _ hsuff
  have hx1 := h_ins hx
  rcases List.mem_append.mp hx1 with h | h
  · rcases List.mem_append.mp (h_apply h) with h2 | h2
    · exact h_orig (h_single h2)
    · exact List.mem_append_right _ h2
  · exact h_orig h
theorem Subst.freeVars_subset_prop_of_tcons (S : SubstInfo)
    (name1 name2 : String) (args1 args2 : List LMonoTy)
    (h_new_constraints : new_constraints = args1.zip args2)
    (relS : ValidSubstRelation new_constraints S)  :
    Subst.freeVars_subset_prop
      [(LMonoTy.tcons name1 args1, LMonoTy.tcons name2 args2)] relS.newS S := by
  obtain ⟨newS, h_newS_subset⟩ := relS
  subst h_new_constraints
  simp only [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars,
    LMonoTy.freeVars, List.append_assoc, List.nil_append] at h_newS_subset ⊢
  have h_zip := @Constraints.freeVars_of_zip_subset args1 args2
  intro x hx
  have hmem := h_newS_subset hx
  rcases List.mem_append.mp hmem with h | h
  · rcases List.mem_append.mp (h_zip h) with h1 | h1
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_append_left _ h1)
  · exact List.mem_append_right _ (List.mem_append_right _ h)
private theorem Constraint.unify_termination_goal_1
    (S : SubstInfo) (id : TyIdentifier)
    (orig_lty lty sty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : HMaps.find? S.subst id = some sty) :
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).uniq.length <
    (Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] ++ S.subst.freeVars).uniq.length ∨
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).uniq.length =
    (Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] ++ S.subst.freeVars).uniq.length ∧
    Constraints.size [(sty, LMonoTy.subst S.subst orig_lty)] <
    Constraints.size [(LMonoTy.ftvar id, orig_lty)] := by
  have h_sty := Subst.freeVars_of_find_subset S.subst _h5
  have h_subst_orig_lty := LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  have h_subset :
        (id :: (sty.freeVars ++
               ((LMonoTy.subst S.subst orig_lty).freeVars ++ S.subst.freeVars))) ⊆
        (id :: (orig_lty.freeVars ++ S.subst.freeVars)) := by
    simp_all
  generalize h_l1 : (sty.freeVars ++
                      ((LMonoTy.subst S.subst orig_lty).freeVars ++ S.subst.freeVars)) = l1 at *
  generalize h_l2 : (orig_lty.freeVars ++ S.subst.freeVars) = l2 at *
  have h_subset_right := @List.length_dedup_append_subset_right _ _ (id :: l1) (id :: l2) h_subset
  have h_len := @List.length_dedup_append_le_left _ _ (id :: l1) (id :: l2)
  have h_id : id ∉ l1 := by
    subst l1; simp_all
    have h_S_ok := S.isWF
    simp [SubstWF] at h_S_ok
    apply And.intro
    · have h_sty_values := HMaps.find?_mem_values S.subst _h5
      have h_id_keys := HMaps.find?_mem_keys S.subst _h5
      exact fun a => h_S_ok id h_id_keys (h_sty a)
    · have h_id_keys := HMaps.find?_mem_keys S.subst _h5
      exact h_S_ok id h_id_keys
  have h_dedup1 := @List.length_dedup_cons_of_not_mem _ _ id l1 h_id
  simp_all
  simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars, h_l1, h_l2]
  omega
  done
private theorem Constraint.unify_termination_goal_2
    (S : SubstInfo) (id : TyIdentifier)
    (orig_lty lty sty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : HMaps.find? S.subst id = some sty) :
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).uniq.length <
    (Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] ++ S.subst.freeVars).uniq.length ∨
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).uniq.length =
    (Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] ++ S.subst.freeVars).uniq.length ∧
    Constraints.size [(sty, LMonoTy.subst S.subst orig_lty)] <
    Constraints.size [(orig_lty, LMonoTy.ftvar id)] := by
  have h1 := @Constraints.freeVars_single_constraint_comm_subset orig_lty (LMonoTy.ftvar id)
  have h2 := @Constraints.freeVars_single_constraint_comm_subset (LMonoTy.ftvar id) orig_lty
  have h3 := Constraint.unify_termination_goal_1 S id orig_lty lty sty h_lty _h4 _h5
  generalize Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] = A at *
  generalize Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] = B at *
  generalize Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] = X at *
  generalize S.subst.freeVars = Y at *
  simp_all [Constraints.size, Constraint.size]
  have h_sub1 : A ++ Y ⊆ B ++ Y := by simp_all
  have h_sub2 : B ++ Y ⊆ A ++ Y := by simp_all
  have h_sub : (B ++ Y).uniq.length = (A ++ Y).uniq.length := by
    exact List.length_dedup_subset_eq (B ++ Y) (A ++ Y) h_sub2 h_sub1
  simp_all
  omega
  done
private theorem Constraint.unify_termination_goal_3
    (S : SubstInfo) (name1 name2 : String) (args1 args2 : List LMonoTy)
    (h_tcons : name1 = name2 ∧ args1.length = args2.length) :
    (Constraints.freeVars (args1.zip args2) ++ S.subst.freeVars).uniq.length <
    (Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] ++
     S.subst.freeVars).uniq.length ∨
    (Constraints.freeVars (args1.zip args2) ++ S.subst.freeVars).uniq.length =
    (Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] ++
     S.subst.freeVars).uniq.length ∧
    Constraints.size (args1.zip args2) <
    Constraints.size [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] := by
  have h_zip_fvs_super := @Constraints.freeVars_of_zip_superset args1 args2 h_tcons.right
  have h_zip_fvs_sub := @Constraints.freeVars_of_zip_subset args1 args2
  have h_zip_size := @Constraints.size_zip_eq args1 args2 h_tcons.right
  have h_fvs_tcons :
    Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] =
    LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2 := by
    simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars]
  have h_size_tcons :
    Constraints.size [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] =
    1 + LMonoTys.size args1 + (1 + LMonoTys.size args2) := by
    simp_all [Constraints.size, Constraint.size, LMonoTy.size]
  simp_all
  clear h_size_tcons h_zip_size h_tcons h_fvs_tcons
  generalize Constraints.freeVars (args1.zip args2) = A at *
  generalize LMonoTys.freeVars args1 = B1 at *
  generalize LMonoTys.freeVars args2 = B2 at *
  generalize S.subst.freeVars = C at *
  have h1 : (A ++ C) ⊆ (B1 ++ (B2 ++ C)) := by
    simp_all
    have : B1 ++ B2 ⊆ B1 ++ (B2 ++ C) := by simp_all
    exact fun _ x => this (h_zip_fvs_sub x)
  have h2 : (B1 ++ (B2 ++ C)) ⊆ (A ++ C) := by
    simp_all
  have h_len_eq := @List.length_dedup_subset_eq _ _
                   (A ++ C) (B1 ++ (B2 ++ C)) h1 h2
  omega
  done
private theorem Constraints.unify_termination_goal_1
    (cs : Constraints) (c : Constraint) (S : SubstInfo) :
    (Constraints.freeVars [c] ++ S.subst.freeVars).uniq.length <
      (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).uniq.length ∨
    (Constraints.freeVars [c] ++ S.subst.freeVars).uniq.length =
        (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).uniq.length ∧
    (Constraints.size [c] < Constraints.size (c :: cs) ∨
     Constraints.size [c] = Constraints.size (c :: cs)) := by
  simp_all [Constraints.freeVars, Constraints.size]
  have h_sub : (c.freeVars ++ S.subst.freeVars) ⊆
               (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) := by
    simp_all
  generalize (c.freeVars ++ S.subst.freeVars) = l1 at *
  generalize (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) = l2 at *
  have h1 : (l1.uniq.length < l2.uniq.length) ∨ (l1.uniq.length = l2.uniq.length) := by
    have := @List.length_dedup_of_subset_le _ _ l1 l2 h_sub
    exact Or.symm (Nat.eq_or_lt_of_le this)
  cases h1 <;> try simp_all
  exact Or.symm (Nat.eq_zero_or_pos (Constraints.size cs))
  done
private theorem Constraints.unify_termination_goal_2
    (cs : Constraints) (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S) :
    (Constraints.freeVars cs ++ relS.newS.subst.freeVars).uniq.length <
    (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).uniq.length ∨
    (Constraints.freeVars cs ++ relS.newS.subst.freeVars).uniq.length =
    (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).uniq.length := by
  obtain ⟨newS, h_subset_prop⟩ := relS
  simp [Subst.freeVars_subset_prop, Constraints.freeVars] at h_subset_prop
  simp [Constraints.freeVars] at *
  have h_sub : (cs.freeVars ++ newS.subst.freeVars) ⊆
               (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) := by
    simp_all
    generalize newS.subst.freeVars = A at *
    generalize c.freeVars = B at *
    generalize cs.freeVars = C at *
    generalize S.subst.freeVars = D at *
    have : B ++ D ⊆ B ++ (C ++ D) := by simp_all
    exact fun _ x => this (h_subset_prop x)
  have := @List.length_dedup_of_subset_le _ _
            (cs.freeVars ++ newS.subst.freeVars)
            (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars))
            h_sub
  omega
  done
inductive UnifyError where
  | ImpossibleToUnify (c : Constraint) (original : Option Constraint := .none)
  | FailedOccursCheck (tyvar : TyIdentifier) (ty : LMonoTy) (c : Constraint) (original : Option Constraint := .none)
def UnifyError.addOriginalConstraint (e : UnifyError) (o : Constraint) : UnifyError :=
  match e with
  | ImpossibleToUnify c _ => ImpossibleToUnify c o
  | FailedOccursCheck tyvar ty c _ => FailedOccursCheck tyvar ty c o
mutual
def Constraint.unifyOne (c : Constraint) (S : SubstInfo) :
  Except UnifyError (ValidSubstRelation [c] S) :=
  let (t1, t2) := c
  if _h1: t1 == t2 then
     have h_sub : Subst.freeVars_subset_prop [(t1, t2)] S S := by
      simp [Subst.freeVars_subset_prop]
    .ok { newS := S, goodSubset := h_sub }
  else
    match _h2: t1, t2 with
    | .ftvar id, orig_lty | orig_lty, .ftvar id => do
      let lty := LMonoTy.subst S.subst orig_lty
      have h_sub1 : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] S S := by
        simp [Subst.freeVars_subset_prop]
      have h_sub2 : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] S S := by
        simp [Subst.freeVars_subset_prop]
      if _h3 : (.ftvar id) == lty then
        .ok { newS := S, goodSubset := by all_goals simp [h_sub1, h_sub2] }
      else if _h4 : id ∈ lty.freeVars then
        .error (.FailedOccursCheck id lty (t1, t2))
      else
        match _h5 : S.subst.find? id with
        | some sty =>
          let relS ← Constraint.unifyOne (sty, lty) S
          have h_sub1_new : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] relS.newS S := by
            exact Subst.freeVars_subset_prop_of_ftvar_id_when_id_in_S
                  S id orig_lty sty lty rfl _h4 _h5 relS
          have h_sub2_new : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] relS.newS S := by
            simp_all [Subst.freeVars_subset_prop_single_constraint_comm]
          .ok { newS := relS.newS,
                goodSubset := by all_goals simp [h_sub1_new, h_sub2_new] }
        | none =>
          have h_id_lty_WF : SubstWF (Subst.singleton id lty) = true :=
            SubstWF.single_subst id lty _h4
          have h_subst_apply_WF : SubstWF (Subst.apply (HMap.single id lty) S.subst) := by
            have := SubstWF.apply_one_substituted_type S.subst S.isWF id orig_lty
            simpa using this
          let new_subst := (Subst.apply (HMap.single id lty) S.subst).insert id lty
          have h' : SubstWF new_subst := by
            exact SubstWF.cons_of_subst_apply S.subst S.isWF id orig_lty lty rfl _h4
          let newS := SubstInfo.mk new_subst h'
          have h_sub1 : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] newS S := by
            exact Subst.freeVars_subset_prop_of_single_constraint S newS new_subst
                   id orig_lty (LMonoTy.subst S.subst orig_lty) rfl rfl h' rfl
          have h_sub2 : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] newS S := by
            simp_all [Subst.freeVars_subset_prop_single_constraint_comm]
          .ok { newS := newS, goodSubset := by all_goals simp [h_sub1, h_sub2] }
    | .bitvec n1, .bitvec n2 =>
      if _h7 : n1 == n2 then
        .ok { newS := SubstInfo.mk [] (by simp [SubstWF, HMaps.keys]), goodSubset := by grind }
      else
        .error (.ImpossibleToUnify (t1, t2))
    | .tcons name1 args1, .tcons name2 args2 => do
      if _h6 : name1 == name2 && args1.length == args2.length then
       let new_constraints := List.zip args1 args2
       let relS ← Constraints.unifyCore new_constraints S
       have h_sub : Subst.freeVars_subset_prop
                    [(LMonoTy.tcons name1 args1, LMonoTy.tcons name2 args2)] relS.newS S := by
         exact Subst.freeVars_subset_prop_of_tcons S name1 name2 args1 args2 rfl relS
       .ok { newS := relS.newS, goodSubset := by simp [h_sub] }
      else
        .error (.ImpossibleToUnify (t1, t2))
    | .bitvec _, .tcons _ _ =>
        .error (.ImpossibleToUnify (t1, t2))
    | .tcons _ _, .bitvec _ =>
        .error (.ImpossibleToUnify (t1, t2))
  termination_by ((((Constraints.freeVars [c]) ++ S.subst.freeVars).uniq.length),
                  Constraints.size [c],
                  0)
  decreasing_by
    all_goals simp_all [Prod.lex_def]
    · exact Constraint.unify_termination_goal_1 S id orig_lty lty sty (by exact rfl) _h4 _h5
    · exact Constraint.unify_termination_goal_2 S id orig_lty lty sty (by exact rfl) _h4 _h5
    · exact Constraint.unify_termination_goal_3 S name1 name2 args1 args2 _h6
def Constraints.unifyCore (cs : Constraints) (S : SubstInfo) :
    Except UnifyError (ValidSubstRelation cs S) := do
  match _h0 : cs with
  | [] => .ok { newS := S, goodSubset := by simpa only [_h0] using Subst.freeVars_subset_prop_of_empty S }
  | c :: c_rest =>
    let relS ← Constraint.unifyOne c S |> .mapError (fun e => UnifyError.addOriginalConstraint e c)
    let new_relS ← Constraints.unifyCore c_rest relS.newS
    .ok { newS := new_relS.newS, goodSubset := by simpa only [_h0] using Subst.freeVars_subset_prop_mk_cons relS new_relS }
  termination_by ((((Constraints.freeVars cs) ++ S.subst.freeVars).uniq.length),
                  Constraints.size cs,
                  1)
  decreasing_by
    all_goals simp_all [Prod.lex_def]
    · exact Constraints.unify_termination_goal_1 c_rest c S
    · exact Constraints.unify_termination_goal_2 c_rest c S relS
end
def Constraints.unify (constraints : Constraints) (S : SubstInfo) :
    Except UnifyError SubstInfo := do
    let relS ← Constraints.unifyCore constraints S
    .ok relS.newS
end
end Lambda

namespace NativeTermUnification
open Lambda Strata.Util
theorem unifyOne_native (c : Constraint) (S : SubstInfo)
    (rel : ValidSubstRelation [c] S) (hok : c.unifyOne S = .ok rel)
    (hS : NativeSubst S.subst) (hc : Shape c.1 ∧ Shape c.2) : NativeSubst rel.newS.subst := by
  revert hS hc
  revert rel
  apply Constraint.unifyOne.induct
    (motive1 := fun c S => ∀ rel, c.unifyOne S = .ok rel → NativeSubst S.subst →
      (Shape c.1 ∧ Shape c.2) → NativeSubst rel.newS.subst)
    (motive2 := fun cs S => ∀ rel, cs.unifyCore S = .ok rel → NativeSubst S.subst →
      (∀ c ∈ cs, Shape c.1 ∧ Shape c.2) → NativeSubst rel.newS.subst)
  · intro S t1 t2 he _ rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · cases h; exact hS
    · exact absurd he ‹_›
  · intro S id orig he _ _ _ he' rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› he
    · cases h; exact hS
  · intro S id orig he _ _ _ he' ho rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  · intro S id orig he _ _ _ he' ho sty hs ih rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› he
    · split at h
      · rename_i sty' hs'
        rw [hs] at hs'; cases hs'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i r hr
          cases h
          exact ih r hr hS ⟨hS sty (HMaps.find?_mem_values S.subst hs),
            shape_subst S.subst hS orig hc.2⟩
      · rename_i hn; rw [hs] at hn; contradiction
  · intro S id orig he _ _ _ he' ho hn _ _ _ns hw _nS _ _ rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› he
    · split at h
      · rename_i sty hs; rw [hn] at hs; contradiction
      · cases h
        exact native_insert _ _ _ (native_apply _ _ _ hS (shape_subst _ hS _ hc.2))
          (shape_subst _ hS _ hc.2)
  · intro S orig id he _ _ _ _ he' rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› he
    · cases h; exact hS
  · intro S orig id he _ _ _ _ he' ho rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  · intro S orig id he _ _ _ _ he' ho sty hs ih rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› he
    · split at h
      · rename_i sty' hs'
        rw [hs] at hs'; cases hs'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i r hr
          cases h
          exact ih r hr hS ⟨hS sty (HMaps.find?_mem_values S.subst hs),
            shape_subst S.subst hS orig hc.1⟩
      · rename_i hn; rw [hs] at hn; contradiction
  · intro S orig id he _ _ _ _ he' ho hn _ _ _ns hw _nS _ _ rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› he
    · split at h
      · rename_i sty hs; rw [hn] at hs; contradiction
      · cases h
        exact native_insert _ _ _ (native_apply _ _ _ hS (shape_subst _ hS _ hc.1))
          (shape_subst _ hS _ hc.1)
  · intro S n1 n2 he hn rel h hS hc; grind
  · intro S n1 n2 he hn rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  · intro S n1 a1 n2 a2 he hm _ ih rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› he
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i r hr
        cases h
        apply ih r hr hS
        intro p hp
        exact ⟨shape_children hc.1 p.1 (List.of_mem_zip hp).1,
          shape_children hc.2 p.2 (List.of_mem_zip hp).2⟩
  · intro S n1 a1 n2 a2 he hm rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  · intro S n nm args he rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  · intro S nm args n he rel h hS hc
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  · intro S rel h hS hc
    rw [Constraints.unifyCore.eq_def] at h; cases h; exact hS
  · intro S c rest ih1 ih2 rel h hS hc
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i one ho
      split at h
      · simp at h
      · rename_i tail ht
        cases h
        apply ih2 one tail ht
        · apply ih1 one
          · cases hcall : c.unifyOne S <;> simp_all [Except.mapError]
          · exact hS
          · exact hc c List.mem_cons_self
        · exact fun p hp => hc p (List.mem_cons_of_mem c hp)
theorem unifyCore_native (cs : Constraints) (S : SubstInfo)
    (rel : ValidSubstRelation cs S) (hok : cs.unifyCore S = .ok rel)
    (hS : NativeSubst S.subst) (hc : ∀ c ∈ cs, Shape c.1 ∧ Shape c.2) :
    NativeSubst rel.newS.subst := by
  induction cs generalizing S with
  | nil => rw [Constraints.unifyCore.eq_def] at hok; cases hok; exact hS
  | cons c rest ih =>
    rw [Constraints.unifyCore.eq_def] at hok; simp only at hok
    simp only [Bind.bind, Except.bind, Except.mapError] at hok
    split at hok
    · simp at hok
    · rename_i one ho
      split at hok
      · simp at hok
      · rename_i tail ht
        cases hok
        apply ih one.newS tail ht
        · apply unifyOne_native c S one
          · cases hcall : c.unifyOne S <;> simp_all [Except.mapError]
          · exact hS
          · exact hc c List.mem_cons_self
        · exact fun p hp => hc p (List.mem_cons_of_mem c hp)
theorem unify_native (cs : Constraints) (S newS : SubstInfo)
    (hok : cs.unify S = .ok newS) (hS : NativeSubst S.subst)
    (hc : ∀ c ∈ cs, Shape c.1 ∧ Shape c.2) : NativeSubst newS.subst := by
  unfold Constraints.unify at hok
  simp only [Bind.bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i rel hr
    cases hok
    exact unifyCore_native cs S rel hr hS hc
end NativeTermUnification
namespace NativeTermUnification
end NativeTermUnification
