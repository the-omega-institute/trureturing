/- GID: D5/S3/Combinatorics/Derangements/TerminalDifference
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Derangements/TerminalDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Centralizer]
   utility: none
   digest: Terminal column difference for the actual derangement triangle. -/

import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Exact cycle-type counting for the terminal-column identity of OEIS A378495. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Derangements.TerminalDifference

open Equiv
open scoped BigOperators

/-- Actual permutations with no fixed points, with labels `Fin n`. -/
def D (n : ℕ) : Finset (Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun p => p ∈ derangements (Fin n))

/-- OEIS A378495: all derangements having no cycle of length `k`. -/
def T (n k : ℕ) : ℕ := by
  classical
  exact ((D n).filter fun p => ∀ c ∈ p.cycleFactorsFinset, c.support.card ≠ k).card

/-- Derangements excluded by the forbidden cycle length. -/
def excluded (n k : ℕ) : Finset (Perm (Fin n)) := by
  classical
  exact (D n).filter fun p => k ∈ p.cycleType

theorem noCycle_iff {n : ℕ} (k : ℕ) (p : Perm (Fin n)) :
    (∀ c ∈ p.cycleFactorsFinset, c.support.card ≠ k) ↔ k ∉ p.cycleType := by
  classical
  simp [Perm.cycleType_def, Multiset.mem_map, ← Finset.mem_def, Function.comp_def]

theorem T_add_excluded (n k : ℕ) : T n k + (excluded n k).card = (D n).card := by
  classical
  simpa [T, excluded, noCycle_iff, Nat.add_comm] using
    (Finset.card_filter_add_card_filter_not (s := D n) (p := fun p => k ∈ p.cycleType))

theorem noFixed_iff_sum {n : ℕ} (p : Perm (Fin n)) :
    p ∈ derangements (Fin n) ↔ p.cycleType.sum = n := by
  classical
  rw [p.sum_cycleType]
  constructor
  · intro h
    have hs : p.support = Finset.univ := by ext x; simp [Perm.mem_support, h x]
    simp [hs]
  · intro h
    have hs : p.support = Finset.univ := Finset.eq_univ_of_card _ (by simpa using h)
    intro x
    exact Perm.mem_support.mp (hs ▸ Finset.mem_univ x)

theorem sum_two {s : Multiset ℕ} (hs : s.sum = 2) (hl : ∀ a ∈ s, 2 ≤ a) :
    s = {2} := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | @cons a s ih =>
    have ha : 2 ≤ a := hl a (by simp)
    have hh : a + s.sum = 2 := by simpa using hs
    have ha2 : a = 2 := by omega
    have hz : s.sum = 0 := by omega
    have he : s = 0 := by
      by_contra hne
      obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hne
      have hb2 : 2 ≤ b := hl b (by simp [hb])
      have hble := Multiset.le_sum_of_mem hb
      omega
    simp [ha2, he]

theorem terminal_cycleType {n : ℕ} (p : Perm (Fin n)) :
    (p ∈ derangements (Fin n) ∧ n ∈ p.cycleType) ↔ p.cycleType = {n} := by
  constructor
  · intro h
    exact Perm.cycleType_of_card_le_mem_cycleType_add_two (by simp) h.2
  · intro h
    refine ⟨(noFixed_iff_sum p).mpr ?_, ?_⟩ <;> simp [h]

theorem penultimate_cycleType {n : ℕ} (hn : 5 ≤ n) (p : Perm (Fin n)) :
    (p ∈ derangements (Fin n) ∧ n - 2 ∈ p.cycleType) ↔
      p.cycleType = {n - 2, 2} := by
  classical
  constructor
  · intro h
    have hs := (noFixed_iff_sum p).mp h.1
    have he := (Multiset.cons_erase h.2).symm
    have hr : (p.cycleType.erase (n - 2)).sum = 2 := by
      rw [he, Multiset.sum_cons] at hs
      omega
    have hz : p.cycleType.erase (n - 2) = {2} :=
      sum_two hr (fun a ha => Perm.two_le_of_mem_cycleType (Multiset.mem_of_mem_erase ha))
    simpa [hz] using he
  · intro h
    refine ⟨(noFixed_iff_sum p).mpr ?_, ?_⟩
    · simp only [h, Multiset.sum_pair]
      omega
    · simp [h]

theorem excluded_terminal_card {n : ℕ} (hn : 5 ≤ n) :
    (excluded n n).card = (n - 1).factorial := by
  classical
  have he : excluded n n = Finset.univ.filter
      (fun p : Perm (Fin n) => p.cycleType = {n}) := by
    ext p
    simp only [excluded, D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact terminal_cycleType p
  rw [he]
  simpa using (Perm.card_of_cycleType_singleton (α := Fin n) (n := n)
    (by omega) (by simp))

theorem excluded_penultimate_mul {n : ℕ} (hn : 5 ≤ n) :
    (excluded n (n - 2)).card * (2 * (n - 2)) = n.factorial := by
  classical
  have he : excluded n (n - 2) = Finset.univ.filter
      (fun p : Perm (Fin n) => p.cycleType = {n - 2, 2}) := by
    ext p
    simp only [excluded, D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact penultimate_cycleType hn p
  rw [he]
  have hne : n - 2 ≠ 2 := by omega
  have hs : ({n - 2, 2} : Multiset ℕ).sum = n := by
    rw [Multiset.sum_pair]
    omega
  have hv : ({n - 2, 2} : Multiset ℕ).sum ≤ Fintype.card (Fin n) ∧
      ∀ c ∈ ({n - 2, 2} : Multiset ℕ), 2 ≤ c := by
    constructor
    · rw [hs, Fintype.card_fin]
    · intro c hc
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> omega
  have hm := Perm.card_of_cycleType_mul_eq (Fin n) ({n - 2, 2} : Multiset ℕ)
  rw [ite_eq_left hv] at hm
  have hd : ((Fintype.card (Fin n) - ({n - 2, 2} : Multiset ℕ).sum).factorial *
      ({n - 2, 2} : Multiset ℕ).prod *
      (∏ c ∈ ({n - 2, 2} : Multiset ℕ).toFinset,
        (({n - 2, 2} : Multiset ℕ).count c).factorial)) = 2 * (n - 2) := by
    rw [Fintype.card_fin, hs, Nat.sub_self]
    simp [Multiset.insert_eq_cons, hne, Ne.symm hne, Nat.mul_comm]
  rw [hd, Fintype.card_fin] at hm
  exact hm

/-- The original universally quantified terminal-column conjecture, with rational subtraction. -/
theorem result (n : ℕ) (hn : 5 ≤ n) :
    (T n (n - 2) : ℚ) - (T n n : ℚ) =
      ((n - 3).factorial : ℚ) * ((n - 4 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) / 2 := by
  have h1 := T_add_excluded n (n - 2)
  have h2 := T_add_excluded n n
  have hc := excluded_terminal_card hn
  have hm := excluded_penultimate_mul hn
  have hdiff : (T n (n - 2) : ℚ) - (T n n : ℚ) =
      ((n - 1).factorial : ℚ) - ((excluded n (n - 2)).card : ℚ) := by
    have h : (T n (n - 2) : ℚ) + ((excluded n (n - 2)).card : ℚ) =
        (T n n : ℚ) + ((n - 1).factorial : ℚ) := by
      exact_mod_cast (show T n (n - 2) + (excluded n (n - 2)).card =
        T n n + (n - 1).factorial by omega)
    linarith only [h]
  have hmQ : ((excluded n (n - 2)).card : ℚ) * (2 * ((n - 2 : ℕ) : ℚ)) =
      (n.factorial : ℚ) := by exact_mod_cast hm
  have hf1 : (n - 1).factorial = (n - 1) * ((n - 2) * (n - 3).factorial) := by
    have h31 : n - 3 + 1 = n - 2 := by omega
    have h21 : n - 2 + 1 = n - 1 := by omega
    rw [← h21, Nat.factorial_succ, ← h31, Nat.factorial_succ]
  have hf : n.factorial = n * ((n - 1) * ((n - 2) * (n - 3).factorial)) := by
    have h : n - 1 + 1 = n := by omega
    conv_lhs => rw [← h, Nat.factorial_succ]
    rw [hf1, h]
  have hn2 : ((n - 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show n - 2 ≠ 0 by omega)
  have hn4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hn1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hn2e : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hf] at hmQ
  push_cast at hmQ
  have hb : ((excluded n (n - 2)).card : ℚ) * 2 =
      (n : ℚ) * ((n - 1 : ℕ) : ℚ) * ((n - 3).factorial : ℚ) := by
    apply (mul_right_cancel₀ hn2)
    nlinarith only [hmQ]
  rw [hdiff, hf1]
  push_cast
  rw [hn4, hn1, hn2e] at *
  nlinarith only [hb]

end D5.S3.Combinatorics.Derangements.TerminalDifference
