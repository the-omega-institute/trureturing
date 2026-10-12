/- GID: D5/S1/Words/Palindromes/ScatteredPalindromeMaximum
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/ScatteredPalindromeMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp maximum of distinct scattered palindromes and its alphabet sizes. -/

/-
proof_shape: content
escape_witness: ScatteredPalindromeMatching.matching_bound
admission_basis: open-problem-resolution (#15450; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15593
Audit targets: result.
Template gap: DependentFamily.realize lacks ArenaRef, original-statement
Implementation, Correspondence, VariationEvidence, Sensitivity and SourceSelection.
DTR reading: DTR-Unregistered (Observe) for result.
Direct frozen dependencies: none.
spal: proof_shape: definition;
  escape_witness: none
  consumers: sp, mem_spal, pal0, outer, spal_wrapped, sp_sum_outer
  Direct frozen dependencies: none.
sp: proof_shape: definition;
  escape_witness: none
  consumers: claim, card_pal0, card_outer_of_extremes, sp_wrapped_fresh, sp_sum_outer,
    outer_card_repeated, sp_decomposition, construct_sp, attainment, sp_residue_bound,
    equality_permitted, bound_and_onlywhen
  Direct frozen dependencies: none.
alphabetSize: proof_shape: definition;
  escape_witness: none
  consumers: claim, word_alphabet_split, construct_alphabet, attainment, equality_permitted,
    bound_and_onlywhen
  Direct frozen dependencies: none.
maxSP: proof_shape: definition;
  escape_witness: none
  consumers: claim, maxSP_even, maxSP_odd, maxSP_add_two, maxSP_succ,
    maxSP_strictMono, maxSP_monotone, maxSP_increment, maxSP_convex, maxSP_ge,
    maxSP_eq_self_iff, construct_sp, attainment, maxSP_telescoping, sp_residue_bound,
    equality_permitted, bound_and_onlywhen
  Direct frozen dependencies: none.
permittedQ: proof_shape: definition;
  escape_witness: none
  consumers: claim, permitted_decomposition, attainment, equality_permitted, bound_and_onlywhen
  Direct frozen dependencies: none.
claim: proof_shape: definition;
  escape_witness: none
  consumers: result
  Direct frozen dependencies: none.
mem_spal: proof_shape: bind-only;
  escape_witness: none
  consumers: mem_pal0, mem_outer, spal_wrapped, sp_wrapped_fresh, sp_sum_outer
  Direct frozen dependencies: none.
maxSP_even: proof_shape: bind-only;
  escape_witness: none
  consumers: maxSP_add_two, maxSP_succ
  Direct frozen dependencies: none.
maxSP_odd: proof_shape: bind-only;
  escape_witness: none
  consumers: maxSP_add_two, maxSP_succ
  Direct frozen dependencies: none.
maxSP_add_two: proof_shape: bind-only;
  escape_witness: none
  consumers: construct_sp, maxSP_telescoping
  Direct frozen dependencies: none.
maxSP_succ: proof_shape: bind-only;
  escape_witness: none
  consumers: maxSP_strictMono, maxSP_increment, maxSP_eq_self_iff
  Direct frozen dependencies: none.
maxSP_strictMono: proof_shape: bind-only;
  escape_witness: none
  consumers: maxSP_monotone
  Direct frozen dependencies: none.
maxSP_monotone: proof_shape: bind-only;
  escape_witness: none
  consumers: sp_residue_bound
  Direct frozen dependencies: none.
maxSP_increment: proof_shape: bind-only;
  escape_witness: none
  consumers: maxSP_convex
  Direct frozen dependencies: none.
maxSP_convex: proof_shape: bind-only;
  escape_witness: none
  consumers: sp_residue_bound
  Direct frozen dependencies: none.
maxSP_ge: proof_shape: bind-only;
  escape_witness: none
  consumers: equality_permitted, bound_and_onlywhen
  Direct frozen dependencies: none.
maxSP_eq_self_iff: proof_shape: content;
  escape_witness: maxSP_eq_self_iff
  consumers: equality_permitted
  Direct frozen dependencies: none.
wrapped: proof_shape: definition;
  escape_witness: none
  consumers: wrapped_injective, wrapped_sublist_iff, wrapped_reverse_eq, outer_eq_of_extremes,
    card_outer_of_extremes, spal_wrapped, sp_wrapped_fresh, Boundary, exists_boundary,
    outer_card_repeated, boundary_positions, construct, construct_length, construct_alphabet
  Direct frozen dependencies: none.
pal0: proof_shape: definition;
  escape_witness: none
  consumers: mem_pal0, card_pal0, outer_eq_of_extremes
  Direct frozen dependencies: none.
outer: proof_shape: definition;
  escape_witness: none
  consumers: mem_outer, outer_eq_of_extremes, card_outer_of_extremes, spal_wrapped,
    outer_card_single, sp_sum_outer, outer_card_repeated, sp_decomposition
  Direct frozen dependencies: none.
mem_pal0: proof_shape: bind-only;
  escape_witness: none
  consumers: outer_eq_of_extremes
  Direct frozen dependencies: none.
card_pal0: proof_shape: bind-only;
  escape_witness: none
  consumers: card_outer_of_extremes
  Direct frozen dependencies: none.
mem_outer: proof_shape: bind-only;
  escape_witness: none
  consumers: outer_eq_of_extremes, spal_wrapped, sp_wrapped_fresh, outer_card_single
  Direct frozen dependencies: none.
wrapped_injective: proof_shape: bind-only;
  escape_witness: none
  consumers: card_outer_of_extremes
  Direct frozen dependencies: none.
sublist_skip_prefix: proof_shape: bind-only;
  escape_witness: none
  consumers: wrapped_sublist_iff
  Direct frozen dependencies: none.
wrapped_sublist_iff: proof_shape: bind-only;
  escape_witness: none
  consumers: outer_eq_of_extremes
  Direct frozen dependencies: none.
wrapped_reverse_eq: proof_shape: bind-only;
  escape_witness: none
  consumers: outer_eq_of_extremes
  Direct frozen dependencies: none.
outer_eq_of_extremes: proof_shape: content;
  escape_witness: outer_eq_of_extremes
  consumers: card_outer_of_extremes
  Direct frozen dependencies: none.
card_outer_of_extremes: proof_shape: content;
  escape_witness: card_outer_of_extremes
  consumers: sp_wrapped_fresh, outer_card_repeated
  Direct frozen dependencies: none.
spal_wrapped: proof_shape: bind-only;
  escape_witness: none
  consumers: sp_wrapped_fresh
  Direct frozen dependencies: none.
sp_wrapped_fresh: proof_shape: content;
  escape_witness: sp_wrapped_fresh
  consumers: construct_sp
  Direct frozen dependencies: none.
exists_last: proof_shape: bind-only;
  escape_witness: none
  consumers: exists_boundary
  Direct frozen dependencies: none.
Boundary: proof_shape: definition;
  escape_witness: none
  consumers: exists_boundary, boundary
  Direct frozen dependencies: none.
exists_boundary: proof_shape: content;
  escape_witness: exists_boundary
  consumers: boundary
  Direct frozen dependencies: none.
boundary: proof_shape: definition;
  escape_witness: none
  consumers: middle, low, high, outer_card_repeated, boundary_positions
  Direct frozen dependencies: none.
middle: proof_shape: definition;
  escape_witness: none
  consumers: outer_card_repeated, sp_decomposition, boundary_positions, sp_residue_bound
  Direct frozen dependencies: none.
low: proof_shape: definition;
  escape_witness: none
  consumers: boundary_positions, word_match_valid, sp_residue_bound
  Direct frozen dependencies: none.
high: proof_shape: definition;
  escape_witness: none
  consumers: boundary_positions, word_match_valid, sp_residue_bound
  Direct frozen dependencies: none.
repeated: proof_shape: definition;
  escape_witness: none
  consumers: outer_card_repeated, sp_decomposition, boundary_positions, word_match_valid,
    word_pair_budget, word_alphabet_split, sp_residue_bound, equality_permitted,
    bound_and_onlywhen
  Direct frozen dependencies: none.
singles: proof_shape: definition;
  escape_witness: none
  consumers: sp_decomposition, word_pair_budget, word_alphabet_split, sp_residue_bound,
    equality_permitted
  Direct frozen dependencies: none.
outer_card_single: proof_shape: bind-only;
  escape_witness: none
  consumers: sp_decomposition
  Direct frozen dependencies: none.
sp_sum_outer: proof_shape: bind-only;
  escape_witness: none
  consumers: sp_decomposition
  Direct frozen dependencies: none.
outer_card_repeated: proof_shape: content;
  escape_witness: outer_card_repeated
  consumers: sp_decomposition
  Direct frozen dependencies: none.
sp_decomposition: proof_shape: content;
  escape_witness: sp_decomposition
  consumers: sp_residue_bound
  Direct frozen dependencies: none.
boundary_positions: proof_shape: content;
  escape_witness: boundary_positions
  consumers: word_match_valid, sp_residue_bound
  Direct frozen dependencies: none.
word_match_valid: proof_shape: content;
  escape_witness: word_match_valid
  consumers: sp_residue_bound
  Direct frozen dependencies: none.
word_pair_budget: proof_shape: bind-only;
  escape_witness: none
  consumers: sp_residue_bound, equality_permitted, bound_and_onlywhen
  Direct frozen dependencies: none.
word_alphabet_split: proof_shape: bind-only;
  escape_witness: none
  consumers: equality_permitted
  Direct frozen dependencies: none.
construct: proof_shape: definition;
  escape_witness: none
  consumers: construct_mem_lt, construct_fresh, construct_length, construct_alphabet,
    construct_sp, attainment
  Direct frozen dependencies: none.
construct_mem_lt: proof_shape: content;
  escape_witness: construct_mem_lt
  consumers: construct_fresh
  Direct frozen dependencies: none.
construct_fresh: proof_shape: content;
  escape_witness: construct_fresh
  consumers: construct_alphabet, construct_sp
  Direct frozen dependencies: none.
construct_length: proof_shape: content;
  escape_witness: construct_length
  consumers: attainment
  Direct frozen dependencies: none.
construct_alphabet: proof_shape: content;
  escape_witness: construct_alphabet
  consumers: attainment
  Direct frozen dependencies: none.
construct_sp: proof_shape: content;
  escape_witness: construct_sp
  consumers: attainment
  Direct frozen dependencies: none.
permitted_decomposition: proof_shape: bind-only;
  escape_witness: none
  consumers: attainment
  Direct frozen dependencies: none.
attainment: proof_shape: content;
  escape_witness: attainment
  consumers: result
  Direct frozen dependencies: none.
maxSP_telescoping: proof_shape: content;
  escape_witness: maxSP_telescoping
  consumers: sp_residue_bound
  Direct frozen dependencies: none.
sp_residue_bound: proof_shape: content;
  escape_witness: sp_residue_bound
  consumers: bound_and_onlywhen
  Direct frozen dependencies: none.
equality_permitted: proof_shape: content;
  escape_witness: equality_permitted
  consumers: bound_and_onlywhen
  Direct frozen dependencies: none.
bound_and_onlywhen: proof_shape: content;
  escape_witness: bound_and_onlywhen
  consumers: result
  Direct frozen dependencies: none.
result: proof_shape: content;
  escape_witness: ScatteredPalindromeMatching.matching_bound
  consumers: settling result
  Direct frozen dependencies: none.
-/

import D5.S1.Words.Palindromes.ScatteredPalindromeMatching
import Mathlib.Data.List.Palindrome
import Mathlib.Tactic.IntervalCases

namespace D5.S1.Words.Palindromes.ScatteredPalindromeMaximum

open D5.S1.Words.Palindromes.ScatteredPalindromeMatching


variable {α : Type*} [DecidableEq α]
def spal (w : List α) : Finset (List α) :=
  w.sublists.toFinset.filter (fun u => u ≠ [] ∧ u.reverse = u)
def sp (w : List α) : ℕ := (spal w).card
def alphabetSize (w : List α) : ℕ := w.toFinset.card
def maxSP (n : ℕ) : ℕ :=
  if n % 2 = 1 then 3 * 2 ^ ((n + 1) / 2 - 1) - 2 else 2 ^ (n / 2 + 1) - 2
def permittedQ (n q : ℕ) : Prop :=
  if n % 2 = 1 then q = (n + 1) / 2 else q = n / 2 ∨ q = n / 2 + 1
def claim : Prop :=
  (∀ (α : Type) [DecidableEq α] (w : List α), sp w ≤ maxSP w.length) ∧
  (∀ n q : ℕ, 1 ≤ n → permittedQ n q → ∃ w : List ℕ,
    w.length = n ∧ alphabetSize w = q ∧ sp w = maxSP n) ∧
  (∀ (α : Type) [DecidableEq α] (w : List α), 1 ≤ w.length →
    sp w = maxSP w.length → permittedQ w.length (alphabetSize w))

@[simp]
private theorem mem_spal {u w : List α} :
    u ∈ spal w ↔ List.Sublist u w ∧ u ≠ [] ∧ u.reverse = u := by
  simp [spal, List.mem_sublists]



@[simp]
private theorem maxSP_even (k : ℕ) : maxSP (2 * k) = 2 ^ (k + 1) - 2 := by
  simp [maxSP]
@[simp]
private theorem maxSP_odd (k : ℕ) : maxSP (2 * k + 1) = 3 * 2 ^ k - 2 := by
  have hd : (2 * k + 1 + 1) / 2 - 1 = k := by omega
  simp [maxSP, hd]

private theorem maxSP_add_two (n : ℕ) : maxSP (n + 2) = 2 * maxSP n + 2 := by
  have hmod := Nat.mod_lt n (by decide : 0 < 2)
  have hp : 1 ≤ 2 ^ (n / 2) := Nat.one_le_pow _ _ (by decide)
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn, show 2 * (n / 2) + 2 = 2 * (n / 2 + 1) by omega]
    simp only [maxSP_even, pow_succ]
    omega
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, show 2 * (n / 2) + 1 + 2 = 2 * (n / 2 + 1) + 1 by omega]
    simp only [maxSP_odd, pow_succ]
    omega

private theorem maxSP_succ (n : ℕ) : maxSP (n + 1) = maxSP n + 2 ^ (n / 2) := by
  have hmod := Nat.mod_lt n (by decide : 0 < 2)
  have hp : 1 ≤ 2 ^ (n / 2) := Nat.one_le_pow _ _ (by decide)
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn, maxSP_even, maxSP_odd]
    simp only [pow_succ]
    simp only [show 2 * (n / 2) / 2 = n / 2 by omega]
    omega
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, show 2 * (n / 2) + 1 + 1 = 2 * (n / 2 + 1) by omega,
      maxSP_even, maxSP_odd]
    simp only [pow_succ]
    simp only [show (2 * (n / 2) + 1) / 2 = n / 2 by omega]
    omega

private theorem maxSP_strictMono : StrictMono maxSP := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [maxSP_succ]
  exact Nat.lt_add_of_pos_right (Nat.pow_pos (by decide))

private theorem maxSP_monotone : Monotone maxSP := maxSP_strictMono.monotone

private theorem maxSP_increment (n : ℕ) : maxSP (n + 1) - maxSP n = 2 ^ (n / 2) := by
  rw [maxSP_succ, Nat.add_sub_cancel_left]

private theorem maxSP_convex : Monotone (fun n => maxSP (n + 1) - maxSP n) := by
  simp only [maxSP_increment]
  intro a b h
  exact Nat.pow_le_pow_right (by decide) (Nat.div_le_div_right h)

private theorem maxSP_ge (n : ℕ) : n ≤ maxSP n := by
  have hp := Nat.lt_two_pow_self (n := n / 2)
  have hmod := Nat.mod_lt n (by decide : 0 < 2)
  unfold maxSP
  split_ifs with ho
  · rw [show (n + 1) / 2 - 1 = n / 2 by omega]
    omega
  · rw [pow_succ]
    omega

private theorem maxSP_eq_self_iff (n : ℕ) : maxSP n = n ↔ n ≤ 2 := by
  constructor
  · intro h
    by_contra hn
    have hn : 3 ≤ n := by omega
    have hgt : ∀ m, 3 ≤ m → m < maxSP m := by
      intro m hm
      induction m with
      | zero => omega
      | succ m ih =>
        by_cases hbase : m = 2
        · subst m; norm_num [maxSP]
        · have hi := ih (by omega)
          rw [maxSP_succ]
          have : 1 ≤ 2 ^ (m / 2) := Nat.one_le_pow _ _ (by decide)
          omega
    have := hgt n hn
    omega
  · intro h
    interval_cases n <;> decide


open List

private def wrapped (a : α) (u : List α) : List α := a :: (u ++ [a])
private def pal0 (w : List α) : Finset (List α) := insert [] (spal w)
private def outer (w : List α) (a : α) : Finset (List α) :=
  (spal w).filter (fun u => u.head? = some a)

@[simp]
private theorem mem_pal0 {u w : List α} :
    u ∈ pal0 w ↔ u <+ w ∧ u.reverse = u := by
  by_cases h : u = []
  · subst u; simp [pal0]
  · simp [pal0, h, mem_spal]

@[simp]
private theorem card_pal0 (w : List α) : (pal0 w).card = sp w + 1 := by
  apply Finset.card_insert_of_notMem
  simp

@[simp]
private theorem mem_outer {u w : List α} {a : α} :
    u ∈ outer w a ↔ u <+ w ∧ u ≠ [] ∧ u.reverse = u ∧ u.head? = some a := by
  simp [outer, mem_spal, and_assoc]

omit [DecidableEq α] in
private theorem wrapped_injective (a : α) : Function.Injective (wrapped a) := by
  intro u v h
  simp only [wrapped, cons.injEq] at h
  exact List.append_cancel_right h.2

omit [DecidableEq α] in
private theorem sublist_skip_prefix {a : α} {p v pre : List α}
    (ha : a ∉ pre) (h : a :: p <+ pre ++ a :: v) : p <+ v := by
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.mp h
  cases l₁ with
  | nil =>
    simp only [List.nil_append] at he
    rw [← he] at h₂
    exact List.cons_sublist_cons.mp h₂
  | cons b l₁ =>
    have hb : b = a := by simpa using (congrArg List.head? he).symm
    subst b
    exact False.elim (ha (h₁.subset (by simp)))

omit [DecidableEq α] in
private theorem wrapped_sublist_iff {a : α} {p mid pre suf : List α}
    (hpre : a ∉ pre) (hsuf : a ∉ suf) :
    wrapped a p <+ pre ++ wrapped a mid ++ suf ↔ p <+ mid := by
  constructor
  · intro h
    have hleft : p ++ [a] <+ mid ++ [a] ++ suf :=
      sublist_skip_prefix hpre (by simpa [wrapped, List.append_assoc] using h)
    have hright : p.reverse <+ mid.reverse :=
      sublist_skip_prefix (pre := suf.reverse) (by simpa using hsuf)
        (by simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using hleft.reverse)
    simpa using hright.reverse
  · intro h
    have hw : wrapped a p <+ wrapped a mid := (h.append_right [a]).cons_cons a
    exact hw.trans ((List.sublist_append_right pre _).trans (List.sublist_append_left _ suf))

omit [DecidableEq α] in
@[simp]
private theorem wrapped_reverse_eq (a : α) (u : List α) :
    (wrapped a u).reverse = wrapped a u ↔ u.reverse = u := by
  simp [wrapped, List.reverse_append, List.reverse_cons]

private theorem outer_eq_of_extremes {a : α} {mid pre suf : List α}
    (hpre : a ∉ pre) (hsuf : a ∉ suf) :
    outer (pre ++ wrapped a mid ++ suf) a =
      insert [a] ((pal0 mid).image (wrapped a)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨hsub, hne, hrev, hhead⟩ := mem_outer.mp hu
    have hpal := List.Palindrome.of_reverse_eq hrev
    cases hpal with
    | nil => exact False.elim (hne rfl)
    | singleton b =>
      have hba : b = a := by simpa using hhead
      subst b; simp
    | cons_concat b hp =>
      have hba : b = a := by simpa using hhead
      subst b
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨_, mem_pal0.mpr ⟨?_, hp.reverse_eq⟩, rfl⟩
      exact (wrapped_sublist_iff hpre hsuf).mp hsub
  · intro hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      apply mem_outer.mpr
      refine ⟨?_, by simp, by simp, by simp⟩
      apply List.singleton_sublist.mpr
      simp [wrapped]
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hsub, hrev⟩ := mem_pal0.mp hp
      apply mem_outer.mpr
      exact ⟨(wrapped_sublist_iff hpre hsuf).mpr hsub,
        by simp [wrapped], (wrapped_reverse_eq _ _).mpr hrev, by simp [wrapped]⟩

private theorem card_outer_of_extremes {a : α} {mid pre suf : List α}
    (hpre : a ∉ pre) (hsuf : a ∉ suf) :
    (outer (pre ++ wrapped a mid ++ suf) a).card = sp mid + 2 := by
  rw [outer_eq_of_extremes hpre hsuf, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ (wrapped_injective a), card_pal0]
  · simp only [Finset.mem_image]
    rintro ⟨p, _, hp⟩
    have hh := congrArg List.length hp
    simp [wrapped] at hh

private theorem spal_wrapped (a : α) (u : List α) :
    spal (wrapped a u) = spal u ∪ outer (wrapped a u) a := by
  ext p
  constructor
  · intro hp
    obtain ⟨hsub, hne, hrev⟩ := mem_spal.mp hp
    by_cases hhead : p.head? = some a
    · exact Finset.mem_union_right _ (mem_outer.mpr ⟨hsub, hne, hrev, hhead⟩)
    · apply Finset.mem_union_left
      apply mem_spal.mpr
      refine ⟨?_, hne, hrev⟩
      have hs : p <+ u ++ [a] := by
        rcases List.sublist_cons_iff.mp hsub with hs | ⟨v, rfl, hs⟩
        · exact hs
        · exact False.elim (hhead (by simp))
      have hr : p.reverse <+ u.reverse := by
        have hsr : p.reverse <+ a :: u.reverse := by simpa using hs.reverse
        rcases List.sublist_cons_iff.mp hsr with hs | ⟨v, he, hs⟩
        · exact hs
        · have hh : p.head? = some a := by rw [hrev] at he; rw [he]; simp
          exact False.elim (hhead hh)
      simpa using hr.reverse
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hs, hn, hr⟩ := mem_spal.mp hp
      exact mem_spal.mpr ⟨(hs.trans (List.sublist_append_left _ [a])).cons a, hn, hr⟩
    · exact Finset.mem_filter.mp hp |>.1

private theorem sp_wrapped_fresh {a : α} {u : List α} (ha : a ∉ u) :
    sp (wrapped a u) = 2 * sp u + 2 := by
  unfold sp
  rw [spal_wrapped, Finset.card_union_of_disjoint]
  · have hc := card_outer_of_extremes (a := a) (mid := u) (pre := []) (suf := [])
      (by simp) (by simp)
    simp only [List.nil_append, List.append_nil] at hc
    rw [hc]
    unfold sp
    omega
  · apply Finset.disjoint_left.mpr
    intro p hp ho
    obtain ⟨hs, hn, hr, hh⟩ := mem_outer.mp ho
    cases p with
    | nil => simp at hn
    | cons b p =>
      have hba : b = a := by simpa using hh
      subst b
      exact ha ((mem_spal.mp hp).1.subset (by simp))

omit [DecidableEq α] in
private theorem exists_last {a : α} {w : List α} (ha : a ∈ w) :
    ∃ mid suf, w = mid ++ a :: suf ∧ a ∉ suf := by
  obtain ⟨s, t, he, hn⟩ := List.eq_append_cons_of_mem (by simpa using ha : a ∈ w.reverse)
  refine ⟨t.reverse, s.reverse, ?_, by simpa using hn⟩
  have h := congrArg List.reverse he
  simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using h

private structure Boundary (w : List α) (a : α) where
  pre : List α
  mid : List α
  suf : List α
  eq_word : w = pre ++ wrapped a mid ++ suf
  not_pre : a ∉ pre
  not_suf : a ∉ suf

private theorem exists_boundary {a : α} {w : List α} (hc : 2 ≤ w.count a) :
    Nonempty (Boundary w a) := by
  induction w with
  | nil => simp at hc
  | cons b w ih =>
    by_cases hb : b = a
    · subst b
      have hcw : 1 ≤ w.count a := by simpa using hc
      have hm : a ∈ w := List.count_pos_iff.mp (by omega)
      obtain ⟨mid, suf, he, hn⟩ := exists_last hm
      exact ⟨⟨[], mid, suf, by simp [wrapped,he], by simp, hn⟩⟩
    · have hcw : 2 ≤ w.count a := by simpa [List.count_cons, hb] using hc
      obtain ⟨d⟩ := ih hcw
      exact ⟨⟨b :: d.pre, d.mid, d.suf, by simp [d.eq_word],
        by simpa [Ne.symm hb] using d.not_pre, d.not_suf⟩⟩

private noncomputable def boundary (w : List α) (a : α) (hc : 2 ≤ w.count a) : Boundary w a :=
  Classical.choice (exists_boundary hc)

private noncomputable def middle (w : List α) (a : α) : List α :=
  if hc : 2 ≤ w.count a then (boundary w a hc).mid else []
private noncomputable def low (w : List α) (a : α) : ℕ :=
  if hc : 2 ≤ w.count a then (boundary w a hc).pre.length else 0
private noncomputable def high (w : List α) (a : α) : ℕ :=
  if hc : 2 ≤ w.count a then
    (boundary w a hc).pre.length + (boundary w a hc).mid.length + 1 else 0

private def repeated (w : List α) : Finset α := w.toFinset.filter (fun a => 2 ≤ w.count a)
private def singles (w : List α) : Finset α := w.toFinset.filter (fun a => w.count a = 1)

private theorem outer_card_single {w : List α} {a : α} (hc : w.count a = 1) :
    (outer w a).card = 1 := by
  have hs : outer w a = {[a]} := by
    ext p
    constructor
    · intro hp
      obtain ⟨hsub, hne, hrev, hhead⟩ := mem_outer.mp hp
      have hpal := List.Palindrome.of_reverse_eq hrev
      cases hpal with
      | nil => simp at hne
      | singleton b =>
        have hb : b=a := by simpa using hhead
        subst b; simp
      | cons_concat b hp =>
        have hb : b=a := by simpa using hhead
        subst b
        have hh := hsub.count_le a
        simp [List.count_append,hc] at hh
    · intro hp
      have he : p = [a] := by simpa using hp
      subst p
      exact mem_outer.mpr ⟨List.singleton_sublist.mpr (List.count_pos_iff.mp (by omega)),
        by simp, by simp, by simp⟩
  rw [hs]; simp

private theorem sp_sum_outer (w : List α) : sp w = ∑ a ∈ w.toFinset, (outer w a).card := by
  classical
  have hh : ∀ p ∈ spal w, p.head? ∈ w.toFinset.image some := by
    intro p hp
    obtain ⟨hs, hn, hr⟩ := mem_spal.mp hp
    cases p with
    | nil => simp at hn
    | cons b p =>
      apply Finset.mem_image.mpr
      exact ⟨b, List.mem_toFinset.mpr (hs.subset (by simp)), rfl⟩
  have h := Finset.card_eq_sum_card_fiberwise (s := spal w) (t := w.toFinset.image some) (f := List.head?) hh
  rw [Finset.sum_image] at h
  · exact h
  · intro a ha b hb hab
    exact Option.some.inj hab

private theorem outer_card_repeated {w : List α} {a : α} (ha : a ∈ repeated w) :
    (outer w a).card = sp (middle w a) + 2 := by
  have hc := (Finset.mem_filter.mp ha).2
  let d := boundary w a hc
  have he := d.eq_word
  have hp := d.not_pre
  have hs := d.not_suf
  have hm : middle w a = d.mid := by simp [middle, hc,d]
  rw [hm]
  calc
    _ = (outer (d.pre ++ wrapped a d.mid ++ d.suf) a).card := congrArg (fun v => (outer v a).card) he
    _ = _ := card_outer_of_extremes hp hs

private theorem sp_decomposition (w : List α) :
    sp w = (singles w).card + ∑ a ∈ repeated w, (2 + sp (middle w a)) := by
  classical
  have hcomp : w.toFinset.filter (fun a => ¬ 2 ≤ w.count a) = singles w := by
    ext a
    simp only [Finset.mem_filter, List.mem_toFinset, singles]
    by_cases ha : a ∈ w
    · have hpos := List.count_pos_iff.mpr ha
      simp only [ha, true_and]
      omega
    · simp [ha]
  have hsplit := Finset.sum_filter_add_sum_filter_not w.toFinset
    (fun a => 2 ≤ w.count a) (fun a => (outer w a).card)
  rw [hcomp] at hsplit
  rw [sp_sum_outer]
  rw [← hsplit]
  have hre : (∑ a ∈ w.toFinset.filter (fun a => 2 ≤ w.count a), (outer w a).card) =
      ∑ a ∈ repeated w, (2 + sp (middle w a)) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [outer_card_repeated ha, Nat.add_comm]
  have hsi : (∑ a ∈ singles w, (outer w a).card) = (singles w).card := by
    calc
      _ = ∑ a ∈ singles w, 1 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact outer_card_single (Finset.mem_filter.mp ha).2
      _ = _ := by simp
  rw [hre,hsi,Nat.add_comm]



open List Finset

private theorem boundary_positions {w : List α} {a : α} (ha : a ∈ repeated w) :
    low w a < high w a ∧ high w a < w.length ∧
    w[low w a]? = some a ∧ w[high w a]? = some a ∧
    (middle w a).length = high w a - low w a - 1 := by
  have hc := (Finset.mem_filter.mp ha).2
  let d := boundary w a hc
  have hl : low w a = d.pre.length := by simp [low,hc,d]
  have hh : high w a = d.pre.length + d.mid.length + 1 := by simp [high,hc,d]
  have hm : middle w a = d.mid := by simp [middle,hc,d]
  have hlen : w.length = d.pre.length + d.mid.length + d.suf.length + 2 := by
    calc
      _ = (d.pre ++ wrapped a d.mid ++ d.suf).length := congrArg List.length d.eq_word
      _ = _ := by simp [wrapped]; omega
  refine ⟨by omega,by omega,?_,?_,by rw [hm]; omega⟩
  · rw [hl]
    calc
      w[d.pre.length]? = (d.pre ++ wrapped a d.mid ++ d.suf)[d.pre.length]? :=
        congrArg (fun v : List α => v[d.pre.length]?) d.eq_word
      _ = some a := by simp [wrapped,List.append_assoc]
  · rw [hh]
    calc
      w[d.pre.length + d.mid.length + 1]? =
          (d.pre ++ wrapped a d.mid ++ d.suf)[d.pre.length + d.mid.length + 1]? :=
        congrArg (fun v : List α => v[d.pre.length + d.mid.length + 1]?) d.eq_word
      _ = some a := by
        simp only [wrapped,List.append_assoc,List.cons_append]
        rw [List.getElem?_append_right (by omega : d.pre.length ≤ d.pre.length + d.mid.length + 1)]
        rw [show d.pre.length + d.mid.length + 1 - d.pre.length = d.mid.length + 1 by omega]
        simp

private theorem word_match_valid (w : List α) : matchValid (repeated w) (low w) (high w) w.length := by
  constructor
  · intro a ha
    have hp := boundary_positions ha
    exact ⟨hp.1,hp.2.1⟩
  · intro a ha b hb
    have hpa := boundary_positions ha
    have hpb := boundary_positions hb
    refine ⟨?_,?_,?_⟩
    · intro he
      have heq : some a=some b := by rw [←hpa.2.2.1,he,hpb.2.2.1]
      exact Option.some.inj heq
    · intro he
      have heq : some a=some b := by rw [←hpa.2.2.2.1,he,hpb.2.2.2.1]
      exact Option.some.inj heq
    · intro he
      have heq : some a=some b := by rw [←hpa.2.2.1,he,hpb.2.2.2.1]
      have hab := Option.some.inj heq
      subst b
      have := hpa.1
      omega

private theorem word_pair_budget (w : List α) : 2 * (repeated w).card + (singles w).card ≤ w.length := by
  have htot := List.sum_toFinset_count_eq_length w
  have hsplit := Finset.sum_filter_add_sum_filter_not w.toFinset
    (fun a => 2 ≤ w.count a) (fun a => w.count a)
  have hcomp : w.toFinset.filter (fun a => ¬ 2 ≤ w.count a) = singles w := by
    ext a
    simp only [Finset.mem_filter,List.mem_toFinset,singles]
    by_cases ha : a ∈ w
    · have hpos := List.count_pos_iff.mpr ha
      simp only [ha,true_and];omega
    · simp [ha]
  rw [hcomp] at hsplit
  have hre : 2 * (repeated w).card ≤ ∑ a ∈ repeated w, w.count a := by
    calc
      _ = ∑ a ∈ repeated w, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun a ha => (Finset.mem_filter.mp ha).2)
  have hsi : (∑ a ∈ singles w, w.count a) = (singles w).card := by
    calc
      _ = ∑ a ∈ singles w, 1 := Finset.sum_congr rfl (fun a ha => (Finset.mem_filter.mp ha).2)
      _ = _ := by simp
  change (∑ a ∈ repeated w, w.count a) + (∑ a ∈ singles w,w.count a) = _ at hsplit
  rw [hsi,htot] at hsplit
  omega

private theorem word_alphabet_split (w : List α) : alphabetSize w = (repeated w).card + (singles w).card := by
  have hc := Finset.card_filter_add_card_filter_not (s := w.toFinset) (fun a => 2 ≤ w.count a)
  have hcomp : w.toFinset.filter (fun a => ¬ 2 ≤ w.count a) = singles w := by
    ext a
    simp only [Finset.mem_filter,List.mem_toFinset,singles]
    by_cases ha : a ∈ w
    · have hpos := List.count_pos_iff.mpr ha
      simp only [ha,true_and];omega
    · simp [ha]
  rw [hcomp] at hc
  exact hc.symm



open List

private def construct : ℕ → ℕ → List ℕ
  | 0, k => List.range k
  | r + 1, k => wrapped (k + r) (construct r k)

private theorem construct_mem_lt (r k : ℕ) : ∀ a ∈ construct r k, a < k + r := by
  induction r with
  | zero => simp [construct]
  | succ r ih =>
    intro a ha
    change a ∈ (k + r) :: (construct r k ++ [k + r]) at ha
    rcases List.mem_cons.mp ha with he | ha
    · omega
    · rcases List.mem_append.mp ha with hm | he
      · have := ih a hm; omega
      · have := List.mem_singleton.mp he; omega

private theorem construct_fresh (r k : ℕ) : k + r ∉ construct r k := by
  intro h
  have := construct_mem_lt r k (k + r) h
  omega

private theorem construct_length (r k : ℕ) : (construct r k).length = 2 * r + k := by
  induction r with
  | zero => simp [construct]
  | succ r ih => simp [construct,wrapped,ih]; omega

private theorem construct_alphabet (r k : ℕ) : alphabetSize (construct r k) = r + k := by
  induction r with
  | zero =>
    simp only [construct,alphabetSize,Nat.zero_add]
    rw [List.toFinset_card_of_nodup (List.nodup_range (n := k)),List.length_range]
  | succ r ih =>
    have hf := construct_fresh r k
    have hs : (wrapped (k + r) (construct r k)).toFinset =
        insert (k + r) (construct r k).toFinset := by
      ext b
      simp [wrapped]
    change (wrapped (k + r) (construct r k)).toFinset.card = r + 1 + k
    rw [hs,Finset.card_insert_of_notMem (by simpa using hf)]
    change alphabetSize (construct r k) + 1 = r + 1 + k
    omega

private theorem construct_sp (r k : ℕ) (hk : k ≤ 2) : sp (construct r k) = maxSP (2 * r + k) := by
  induction r with
  | zero =>
    interval_cases k <;> decide
  | succ r ih =>
    simp only [construct]
    rw [sp_wrapped_fresh (construct_fresh r k), ih]
    rw [show 2 * (r + 1) + k=(2 * r + k) + 2 by omega,maxSP_add_two]

private theorem permitted_decomposition {n q : ℕ} (hn : 1 ≤ n) (hq : permittedQ n q) :
    ∃ r k, k ≤ 2 ∧ n = 2 * r + k ∧ q = r + k := by
  unfold permittedQ at hq
  have hmod := Nat.mod_lt n (by decide : 0 < 2)
  split_ifs at hq with ho
  · refine ⟨n/2,1,by omega,by omega,by omega⟩
  · rcases hq with hq | hq
    · exact ⟨n/2,0,by omega,by omega,by omega⟩
    · exact ⟨n/2 - 1,2,by omega,by omega,by omega⟩

private theorem attainment (n q : ℕ) (hn : 1 ≤ n) (hq : permittedQ n q) :
    ∃ w : List ℕ, w.length=n ∧ alphabetSize w=q ∧ sp w=maxSP n := by
  obtain ⟨r,k,hk,he,hq⟩ := permitted_decomposition hn hq
  refine ⟨construct r k,?_,?_,?_⟩
  · rw [construct_length,he]
  · rw [construct_alphabet,hq]
  · rw [construct_sp r k hk,he]



open Finset

private theorem maxSP_telescoping (n r : ℕ) (hr : 2 * r ≤ n) :
    nestSum maxSP n r + 2 * r + maxSP (n - 2 * r) = maxSP n := by
  induction r generalizing n with
  | zero => simp [nestSum]
  | succ r ih =>
    have hn : 2 ≤ n := by omega
    have hi := ih (n - 2) (by omega)
    have hrec := maxSP_add_two (n - 2)
    rw [show n - 2 + 2=n by omega] at hrec
    rw [nestSum_succ]
    rw [show n - 2 * (r + 1)=n - 2 - 2 * r by omega]
    omega

private theorem sp_residue_bound (w : List α)
    (ih : ∀ v : List α, v.length < w.length → sp v ≤ maxSP v.length) :
    sp w + maxSP (w.length - 2 * (repeated w).card) ≤ (singles w).card + maxSP w.length := by
  have hpair := word_pair_budget w
  have hmatch := matching_bound maxSP maxSP_monotone maxSP_convex
    (repeated w) (low w) (high w) w.length (word_match_valid w)
  have hlocal : ∀ a ∈ repeated w, sp (middle w a) ≤ maxSP (high w a - low w a - 1) := by
    intro a ha
    have hp := boundary_positions ha
    have hm := hp.2.2.2.2
    have hv : (middle w a).length < w.length := by omega
    simpa [hm] using ih (middle w a) hv
  have hsum : (∑ a ∈ repeated w, (2 + sp (middle w a))) ≤
      2 * (repeated w).card + nestSum maxSP w.length (repeated w).card := by
    calc
      _ ≤ ∑ a ∈ repeated w, (2 + maxSP (high w a - low w a - 1)) :=
        Finset.sum_le_sum (fun a ha => Nat.add_le_add_left (hlocal a ha) 2)
      _ = 2 * (repeated w).card + ∑ a ∈ repeated w,maxSP (high w a - low w a - 1) := by
        rw [Finset.sum_add_distrib]
        simp [Nat.mul_comm]
      _ ≤ _ := Nat.add_le_add_left hmatch _
  have ht := maxSP_telescoping w.length (repeated w).card (by omega)
  rw [sp_decomposition]
  omega

private theorem equality_permitted (w : List α)
    (hres : sp w + maxSP (w.length - 2 * (repeated w).card) ≤ (singles w).card + maxSP w.length)
    (he : sp w = maxSP w.length) : permittedQ w.length (alphabetSize w) := by
  have hb := word_pair_budget w
  have hg := maxSP_ge (w.length - 2 * (repeated w).card)
  have heq : maxSP (w.length - 2 * (repeated w).card) = w.length - 2 * (repeated w).card := by omega
  have hk := (maxSP_eq_self_iff _).mp heq
  have hs : (singles w).card = w.length - 2 * (repeated w).card := by omega
  have ha := word_alphabet_split w
  have hmod := Nat.mod_lt w.length (by decide : 0 < 2)
  unfold permittedQ
  split_ifs <;> omega

private theorem bound_and_onlywhen (w : List α) : sp w ≤ maxSP w.length ∧
    (sp w = maxSP w.length → permittedQ w.length (alphabetSize w)) := by
  have hmain : ∀ n, ∀ w : List α, w.length = n →
      sp w ≤ maxSP w.length ∧
      (sp w = maxSP w.length → permittedQ w.length (alphabetSize w)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hwn
      have hl : ∀ v : List α, v.length < w.length → sp v ≤ maxSP v.length := by
        intro v hv
        exact (ih v.length (by omega) v rfl).1
      have hres := sp_residue_bound w hl
      have hpair := word_pair_budget w
      have hge := maxSP_ge (w.length - 2 * (repeated w).card)
      exact ⟨by omega, equality_permitted w hres⟩
  exact hmain w.length w rfl

theorem result : claim := by
  constructor
  · intro α _ w
    exact (bound_and_onlywhen w).1
  · constructor
    · exact attainment
    · intro α _ w _ he
      exact (bound_and_onlywhen w).2 he


end D5.S1.Words.Palindromes.ScatteredPalindromeMaximum
