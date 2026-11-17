/- GID: D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrdinaryAscent/DyckNarayana
   mirror-E: none(waiver:licensed-dyck-narayana-supplier)
   anchors: []
   utility: none
   digest: Licensed suffix-ballot enumeration of actual Mathlib Dyck-word peak fibers. -/

/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The Narayana distribution of Dyck-word peaks

`DyckWord.peakCount` counts the `UD` factors of a Dyck word, and `Nat.narayana n k` is the
Narayana number `C(n,k) C(n,k-1) / n` (with `N(0,0) = 1`).
`DyckWord.card_semilength_peakCount`: the Dyck words of semilength `n` with `k` peaks number
`Nat.narayana n k`, except for `(n, k) = (1, 0)` (`card_semilength_one_peakCount_zero`), where
the natural-number formula gives `1`.  The proof counts suffix-ballot words by first letter;
it was found by Aristotle (Harmonic) and adapted.
-/

@[expose] public section

open List
open DyckStep

/-- The Narayana number, with the empty-path convention `N(0,0) = 1`. -/
def Nat.narayana (n k : ℕ) : ℕ :=
  if n = 0 then if k = 0 then 1 else 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

namespace DyckWord

/-- The number of `UD` factors in a list of Dyck steps. -/
def peakCountList : List DyckStep → ℕ
  | [] => 0
  | U :: D :: l => peakCountList l + 1
  | _ :: l => peakCountList l

/-- The number of `UD` peaks in a Dyck word. -/
def peakCount (p : DyckWord) : ℕ := peakCountList p.toList

/-! ### Proof infrastructure

We count *suffix-ballot* words (every suffix has at least as many `D`s as `U`s) with
`a` copies of `U`, `b` copies of `D` and a given number of peaks, split by first letter.
Prepending a letter gives linear recurrences, whose solutions are explicit
differences of products of binomial coefficients (verified via Pascal's rule).
The balanced suffix-ballot words are exactly the Dyck words. -/

private def Good (l : List DyckStep) : Prop := ∀ i, (l.drop i).count U ≤ (l.drop i).count D

private lemma good_nil : Good [] := by intro i; simp

private lemma good_cons {x : DyckStep} {l : List DyckStep} :
    Good (x :: l) ↔ Good l ∧ (x::l).count U ≤ (x::l).count D := by
  constructor
  · intro h; exact ⟨fun i => h (i+1), h 0⟩
  · rintro ⟨h1, h2⟩ (_|i)
    exacts [h2, h1 i]

private def S : ℕ → ℕ → Finset (List DyckStep)
  | 0, 0 => {[]}
  | _+1, 0 => ∅
  | 0, b+1 => (S 0 b).image (D :: ·)
  | a+1, b+1 => (S (a+1) b).image (D :: ·) ∪
      (if a+1 ≤ b+1 then (S a (b+1)).image (U :: ·) else ∅)
termination_by a b => a + b

private lemma mem_S {l : List DyckStep} {a b : ℕ} :
    l ∈ S a b ↔ l.count U = a ∧ l.count D = b ∧ Good l := by
  induction l generalizing a b with
  | nil =>
    cases a <;> cases b <;> simp [S, good_nil]
    split_ifs <;> simp
  | cons x l ih =>
    cases x with
    | U => cases a <;> cases b <;> simp [S, good_cons] <;> grind
    | D =>
      cases a with
      | zero =>
        cases b <;> simp [S, good_cons]
        grind
      | succ a =>
        cases b with
        | zero => simp [S, good_cons]
        | succ b =>
          simp only [S, add_le_add_iff_right, Finset.mem_union, Finset.mem_image,
            cons.injEq, true_and, exists_eq_right, ih, ne_eq, reduceCtorEq,
            not_false_eq_true, count_cons_of_ne, count_cons_self,
            Nat.add_right_cancel_iff, good_cons]
          have hEmpty : D :: l ∉ (∅ : Finset (List DyckStep)) := Finset.notMem_empty _
          have hGood : ∀ r : List DyckStep, Good r → r.count U ≤ r.count D := by
            intro r hr
            simpa using hr 0
          split_ifs <;> simp only [hEmpty] at * <;> grind

private lemma good_le {l : List DyckStep} (h : Good l) : l.count U ≤ l.count D := by
  simpa using h 0

private lemma S_le {l : List DyckStep} {a b : ℕ} (h : l ∈ S a b) : a ≤ b := by
  obtain ⟨rfl, rfl, h'⟩ := mem_S.1 h
  exact good_le h'

lemma pc_U (l : List DyckStep) :
    peakCountList (U :: l) = peakCountList l + if l.head? = some D then 1 else 0 := by
  rcases l with _ | ⟨_ | _, l⟩ <;> simp [peakCountList]

lemma pc_D (l : List DyckStep) : peakCountList (D :: l) = peakCountList l := by
  rcases l with _ | ⟨_ | _, l⟩ <;> simp [peakCountList]

private def cU (a b k : ℕ) : ℕ :=
  ((S a b).filter (fun l => l.head? = some U ∧ peakCountList l = k)).card
private def cD (a b k : ℕ) : ℕ :=
  ((S a b).filter (fun l => l.head? = some D ∧ peakCountList l = k)).card
private def cT (a b k : ℕ) : ℕ := ((S a b).filter (fun l => peakCountList l = k)).card

private lemma card_split (s : Finset (List DyckStep)) (Q : List DyckStep → Prop)
    [DecidablePred Q] :
    (s.filter Q).card = (s.filter (fun l => l.head? = some U ∧ Q l)).card +
      (s.filter (fun l => l.head? = some D ∧ Q l)).card +
      (s.filter (fun l => l = [] ∧ Q l)).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases l with _ | ⟨_ | _, l⟩ <;> simp

private lemma card_nil (a b k : ℕ) :
    ((S a b).filter (fun l => l = [] ∧ peakCountList l = k)).card =
      if a = 0 ∧ b = 0 ∧ k = 0 then 1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨[], ?_⟩
    ext l
    simp only [Finset.mem_filter, mem_S, Finset.mem_singleton]
    constructor
    · exact fun h => h.2.1
    · rintro rfl; simp [good_nil, peakCountList]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro l hl ⟨rfl, hk⟩
    simp only [mem_S, count_nil, peakCountList] at hl hk
    lia

private lemma cT_eq (a b k : ℕ) :
    cT a b k = cU a b k + cD a b k + if a = 0 ∧ b = 0 ∧ k = 0 then 1 else 0 := by
  unfold cT cU cD
  rw [card_split _ (fun l => peakCountList l = k), card_nil]

private lemma cD_succ (a b k : ℕ) : cD a (b+1) k = cT a b k := by
  unfold cD cT
  rw [show (S a (b+1)).filter (fun l => l.head? = some D ∧ peakCountList l = k) =
      ((S a b).filter (fun l => peakCountList l = k)).image (D :: ·) from ?_]
  · exact Finset.card_image_of_injective _ (List.cons_injective)
  ext l
  rcases l with _ | ⟨_ | _, l⟩
  · simp only [Finset.mem_filter, head?_nil, reduceCtorEq, false_and, and_false,
      Finset.mem_image, exists_const]
  · simp only [Finset.mem_filter, head?_cons, Option.some.injEq, reduceCtorEq,
      false_and, and_false, Finset.mem_image, cons.injEq, exists_const]
  · simp only [Finset.mem_filter, head?_cons, reduceCtorEq,
      true_and, Finset.mem_image, cons.injEq, exists_eq_right, mem_S, good_cons, pc_D,
      count_cons_self, count_cons_of_ne, ne_eq, not_false_eq_true,
      Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨⟨hu, hd, hg, htotal⟩, hk⟩
      exact ⟨⟨hu, hd, hg⟩, hk⟩
    · rintro ⟨⟨hu, hd, hg⟩, hk⟩
      refine ⟨⟨hu, hd, hg, ?_⟩, hk⟩
      have hle := good_le hg
      lia

private lemma cD_zero (a k : ℕ) : cD a 0 k = 0 := by
  unfold cD
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro (_ | ⟨_ | _, l⟩) hl ⟨hh, _⟩ <;> simp [mem_S] at hl hh

private lemma cU_zero (b k : ℕ) : cU 0 b k = 0 := by
  unfold cU
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro (_ | ⟨_ | _, l⟩) hl ⟨hh, _⟩ <;> simp [mem_S] at hl hh

private lemma cU_gt {a b : ℕ} (h : b < a) (k : ℕ) : cU a b k = 0 := by
  unfold cU
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l hl
  have := S_le hl
  lia

private lemma cD_gt {a b : ℕ} (h : b < a) (k : ℕ) : cD a b k = 0 := by
  unfold cD
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l hl
  have := S_le hl
  lia

private lemma cU_succ_aux {a b : ℕ} (hab : a + 1 ≤ b) (k : ℕ) :
    cU (a+1) b k = cU a b k +
      ((S a b).filter (fun l => l.head? = some D ∧ peakCountList l + 1 = k)).card := by
  unfold cU
  rw [show (S (a+1) b).filter (fun l => l.head? = some U ∧ peakCountList l = k) =
      ((S a b).filter (fun l => peakCountList l + (if l.head? = some D then 1 else 0) = k)).image
        (U :: ·) from ?_]
  · rw [Finset.card_image_of_injective _ (List.cons_injective), card_split]
    have h0 : ((S a b).filter (fun l => l = [] ∧
        peakCountList l + (if l.head? = some D then 1 else 0) = k)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro l hl ⟨rfl, -⟩
      simp only [mem_S, count_nil] at hl
      lia
    rw [h0, add_zero]
    congr 2 <;> apply Finset.filter_congr <;> intro l _ <;> simp_all
  ext l
  rcases l with _ | ⟨_ | _, l⟩
  · simp only [Finset.mem_filter, mem_S, count_nil, Nat.right_eq_add,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, false_and, head?_nil, reduceCtorEq,
      and_self, Finset.mem_image, exists_const]
  · simp only [Finset.mem_filter, mem_S, count_cons_self, Nat.add_right_cancel_iff,
      ne_eq, reduceCtorEq, not_false_eq_true, count_cons_of_ne, good_cons, head?_cons,
      pc_U, true_and, Finset.mem_image, cons.injEq, exists_eq_right,
      and_congr_left_iff, and_congr_right_iff, and_iff_left_iff_imp]
    intro _ hu hd hg
    lia
  · simp only [Finset.mem_filter, mem_S, ne_eq, reduceCtorEq, not_false_eq_true,
      count_cons_of_ne, count_cons_self, good_cons, head?_cons, Option.some.injEq,
      false_and, and_false, Finset.mem_image, cons.injEq, exists_const]

private lemma cU_succ (a b k : ℕ) :
    cU (a+1) b k = if a + 1 ≤ b then cU a b k + (if k = 0 then 0 else cD a b (k-1)) else 0 := by
  split_ifs with hab hk
  · subst hk
    rw [cU_succ_aux hab]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
    rw [cU_succ_aux hab]
    simp only [cD, add_tsub_cancel_right, add_left_inj]
  · exact cU_gt (by lia) k


private def fT (a b k : ℕ) : ℤ :=
  if a = 0 then (if k = 0 then 1 else 0)
  else (a.choose k * b.choose k : ℤ) - ((a-1).choose k * (b+1).choose k : ℤ)

private def fU (a b k : ℕ) : ℤ :=
  if a = 0 ∨ b = 0 ∨ k = 0 then 0
  else (a.choose k * (b-1).choose (k-1) : ℤ) - ((a-1).choose k * b.choose (k-1) : ℤ)

private def fD (a b k : ℕ) : ℤ := if b = 0 then 0 else fT a (b-1) k

private lemma id1 {a b : ℕ} (hab : a ≤ b) (k : ℕ) :
    fU a b k + fD a b k + (if a = 0 ∧ b = 0 ∧ k = 0 then 1 else 0) = fT a b k := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [fU, fD, fT]
    · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by lia⟩
      simp [fU, fD, fT]
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by lia⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by lia⟩
  rcases k with _ | k
  · simp [fU, fD, fT]
  · have h1 := Nat.choose_succ_succ b k
    have h2 := Nat.choose_succ_succ (b+1) k
    simp only [fU, fD, fT, Nat.add_one_ne_zero, ite_false, or_self, add_tsub_cancel_right,
      and_false, add_zero]
    rw [h2, h1]
    push_cast
    ring

private lemma id2 {a b : ℕ} (hab : a + 1 ≤ b) (k : ℕ) :
    fU a b k + (if k = 0 then 0 else fD a b (k-1)) = fU (a+1) b k := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by lia⟩
  rcases k with _ | k
  · simp [fU]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases k with _ | k
    · simp [fU, fD, fT]
    · simp [fU, fD, fT, Nat.choose_eq_zero_of_lt (by lia : 1 < k + 1 + 1)]
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by lia⟩
  have h1 := Nat.choose_succ_succ a k
  have h2 := Nat.choose_succ_succ (a+1) k
  simp only [fU, fD, fT, Nat.add_one_ne_zero, ite_false, or_self, add_tsub_cancel_right]
  rw [h2, h1]
  push_cast
  ring

private lemma id3 {a : ℕ} (ha : a ≠ 0) (k : ℕ) : fT a (a-1) k = 0 := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by lia⟩
  simp [fT, mul_comm]


private lemma main_ind (n : ℕ) : ∀ a b, a + b = n → a ≤ b → ∀ k,
    (cU a b k : ℤ) = fU a b k ∧ (cD a b k : ℤ) = fD a b k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn hab k
  constructor
  · rcases a with _ | a
    · simp [cU_zero, fU]
    · rw [cU_succ, ite_eq_left hab, ← id2 hab]
      obtain ⟨h1, h2⟩ := ih (a + b) (by lia) a b rfl (by lia) k
      split_ifs with hk
      · simp [h1]
      · obtain ⟨-, h3⟩ := ih (a + b) (by lia) a b rfl (by lia) (k - 1)
        push_cast
        rw [h1, h3]
  · rcases b with _ | b
    · simp [cD_zero, fD]
    · rw [cD_succ, cT_eq]
      simp only [fD, Nat.add_one_ne_zero, ite_false, add_tsub_cancel_right]
      rcases Nat.lt_or_ge b a with h | h
      · have ha : a = b + 1 := by lia
        have h3 := id3 (Nat.add_one_ne_zero b) k
        rw [add_tsub_cancel_right] at h3
        rw [cU_gt h, cD_gt h, ite_eq_right (by lia), ha, h3]
        simp
      · obtain ⟨h1, h2⟩ := ih (a + b) (by lia) a b rfl h k
        rw [← id1 h k]
        push_cast
        rw [h1, h2]

private lemma cT_diag (n k : ℕ) : (cT n n k : ℤ) = fT n n k := by
  obtain ⟨h1, h2⟩ := main_ind (n + n) n n rfl le_rfl k
  rw [cT_eq, ← id1 le_rfl k]
  push_cast
  rw [h1, h2]

private lemma fT_diag {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (n : ℤ) * fT n n k = (n.choose k * n.choose (k - 1) : ℕ) := by
  rw [← id1 le_rfl k, ite_eq_right (by lia)]
  have : fD n n k = 0 := by simp [fD, hn, id3 hn]
  rw [this]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
  simp only [fU, Nat.add_one_ne_zero, ite_false, or_self, add_tsub_cancel_right, add_zero]
  rcases Nat.lt_or_ge m j with hj | hj
  · rw [Nat.choose_eq_zero_of_lt (by lia : m + 1 < j + 1), Nat.choose_eq_zero_of_lt hj,
      Nat.choose_eq_zero_of_lt (by lia : m < j + 1)]
    simp
  have e1 := Nat.add_one_mul_choose_eq m j
  have e2 := Nat.choose_succ_right_eq (m + 1) j
  have e3 := Nat.choose_mul_succ_eq m (j + 1)
  have e1' : ((m : ℤ) + 1) * (m.choose j : ℕ) = ((m + 1).choose (j + 1) : ℕ) * ((j : ℤ) + 1) := by
    exact_mod_cast e1
  have e2' : (((m + 1).choose (j + 1) : ℕ) : ℤ) * ((j : ℤ) + 1) =
      ((m + 1).choose j : ℕ) * ((m : ℤ) + 1 - j) := by
    rw [show (m : ℤ) + 1 - j = ((m + 1 - j : ℕ) : ℤ) by lia]
    exact_mod_cast e2
  have e3' : ((m.choose (j + 1) : ℕ) : ℤ) * ((m : ℤ) + 1) =
      ((m + 1).choose (j + 1) : ℕ) * ((m : ℤ) - j) := by
    rw [show (m : ℤ) - j = ((m + 1 - (j + 1) : ℕ) : ℤ) by lia]
    exact_mod_cast e3
  push_cast
  set A : ℤ := (((m + 1).choose (j + 1) : ℕ) : ℤ)
  set E : ℤ := (((m + 1).choose j : ℕ) : ℤ)
  calc ((m : ℤ) + 1) * (A * (m.choose j : ℕ) - (m.choose (j + 1) : ℕ) * E)
      = A * (((m : ℤ) + 1) * (m.choose j : ℕ)) - E * ((m.choose (j + 1) : ℕ) * ((m : ℤ) + 1)) := by
        ring
    _ = A * (A * ((j : ℤ) + 1)) - E * (A * ((m : ℤ) - j)) := by rw [e1', e3']
    _ = A * (E * ((m : ℤ) + 1 - j)) - E * (A * ((m : ℤ) - j)) := by rw [e2']
    _ = A * E := by ring

private lemma narayana_eq_cT {n k : ℕ} (h : ¬(n = 1 ∧ k = 0)) : Nat.narayana n k = cT n n k := by
  have hc := cT_diag n k
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [fT, ite_true] at hc
    simp only [Nat.narayana, ite_true]
    split_ifs at hc ⊢ <;> lia
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : cT n n 0 = 0 := by
      have : fT n n 0 = 0 := by simp [fT, hn.ne']
      lia
    rw [h0, Nat.narayana, ite_eq_right hn.ne']
    simp only [Nat.choose_zero_right, zero_tsub, mul_one]
    exact Nat.div_eq_of_lt (by lia)
  · have h2 := fT_diag hn.ne' hk.ne'
    rw [← hc] at h2
    have h3 : n * cT n n k = n.choose k * n.choose (k - 1) := by exact_mod_cast h2
    rw [Nat.narayana, ite_eq_right hn.ne', ← h3, Nat.mul_div_cancel_left _ hn]

private lemma good_of_dyck (p : DyckWord) : Good p.toList := by
  intro i
  have h1 := p.count_U_eq_count_D
  have h2 := p.count_D_le_count_U i
  have e1 := congrArg (count U) (take_append_drop i p.toList)
  have e2 := congrArg (count D) (take_append_drop i p.toList)
  rw [count_append] at e1 e2
  lia

private lemma take_le_of_good {l : List DyckStep} (h1 : l.count U = l.count D) (h2 : Good l)
    (i : ℕ) : (l.take i).count D ≤ (l.take i).count U := by
  have h3 := h2 i
  have e1 := congrArg (count U) (take_append_drop i l)
  have e2 := congrArg (count D) (take_append_drop i l)
  rw [count_append] at e1 e2
  lia

private def peakEquiv (n k : ℕ) :
    {p : {p : DyckWord // p.semilength = n} // p.1.peakCount = k} ≃
      ((S n n).filter (fun l => peakCountList l = k)) where
  toFun p := ⟨p.1.1.toList, by
    rw [Finset.mem_filter, mem_S]
    refine ⟨⟨p.1.2, ?_, good_of_dyck _⟩, p.2⟩
    rw [← p.1.1.count_U_eq_count_D]
    exact p.1.2⟩
  invFun l := by
    have hl := (Finset.mem_filter.1 l.2).1
    rw [mem_S] at hl
    refine ⟨⟨⟨l.1, ?_, take_le_of_good ?_ hl.2.2⟩, hl.1⟩, (Finset.mem_filter.1 l.2).2⟩ <;> lia
  left_inv p := rfl
  right_inv l := rfl

private lemma card_eq_cT (n k : ℕ) :
    Fintype.card {p : {p : DyckWord // p.semilength = n} // p.1.peakCount = k} = cT n n k := by
  rw [Fintype.card_congr (peakEquiv n k), Fintype.card_coe]
  rfl

/-!
The uncorrected quotient identity fails at `(n, k) = (2, 0)`, and the
uncorrected fibre identity fails at `(n, k) = (1, 0)`, because subtraction
in `k - 1` is truncated.  The hypotheses below exclude exactly these
boundary failures.
-/

/-- The binomial quotient identity for positive semilength.
Corrected: the hypothesis `hk : k ≠ 0` was added (the original is false for `n = 2, k = 0`). -/
theorem _root_.Nat.narayana_mul (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) :
    n * Nat.narayana n k = Nat.choose n k * Nat.choose n (k - 1) := by
  have h2 := fT_diag hn hk
  rw [← cT_diag] at h2
  rw [narayana_eq_cT (by lia)]
  exact_mod_cast h2

/-- The number of Dyck words of semilength `n` with exactly `k` peaks is the
Narayana number.
Corrected: the hypothesis `¬(n = 1 ∧ k = 0)` was added (the original is false there). -/
theorem card_semilength_peakCount (n k : ℕ) (h : ¬(n = 1 ∧ k = 0)) :
    Fintype.card {p : {p : DyckWord // p.semilength = n} // p.1.peakCount = k} =
      Nat.narayana n k := by
  rw [card_eq_cT, narayana_eq_cT h]

/-- The excluded case of `card_semilength_peakCount`: the Dyck word `UD` has one peak. -/
theorem card_semilength_one_peakCount_zero :
    Fintype.card {p : {p : DyckWord // p.semilength = 1} // p.1.peakCount = 0} = 0 := by
  rw [card_eq_cT]
  simp [cT, S, peakCountList]

end DyckWord

/-
Adapted from Per Alexandersson, RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean,
commit 27276f93bbaf6b46bce689bca110bbacab1bba6b (2026).
https://github.com/PerAlexandersson/RealRooted/blob/27276f93bbaf6b46bce689bca110bbacab1bba6b/RealRooted/Mathlib/Combinatorics/Enumerative/DyckStatistics.lean
Source SHA256: 0421ff0edbddb5c6616719282832e3cb1081be0cea91b1a29b19ddd6d2f6708b.
Changes: project GID header; expose pc_U and pc_D for the ordinary-word statistic consumer;
retain the complete Apache-2.0 license below. No broad package dependency or pin upgrade.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!) The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
