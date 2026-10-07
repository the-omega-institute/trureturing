/- GID: D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/MatharCentralBinomialTransformRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Mathar's recurrence holds for the binomial sum defining OEIS A113409. -/

/-
proof_shape: result: content
escape_witness: form (2): result itself. The live induction tr_recurrence derives the
  unbounded recurrence from the Pascal and weighted-transform identities and the
  parity recurrence for C(k, floor(k/2)); its induction hypothesis supplies a new
  recurrence fact, not an instance or normalization of a pinned upstream recurrence.
admission_basis: open-problem-resolution (#13334; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

namespace D5.S1.Recurrence.MatharCentralBinomialTransformRecurrence
open Finset

/-- OEIS A113409, defined by the formula-field binomial sum. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose (n - k) k * Nat.choose k (k / 2)

/-- Mathar's conjectured recurrence for every natural index at least four. -/
def claim : Prop := ∀ n : ℕ, 4 ≤ n →
  ((n : ℤ) + 2) * a n - 2 * ((n : ℤ) + 1) * a (n - 1) +
    ((n : ℤ) - 4) * a (n - 2) + 2 * a (n - 3) +
    4 * (2 - (n : ℤ)) * a (n - 4) = 0

/-- The binomial transform satisfies Mathar's recurrence. -/
theorem result : claim := by
  let t (n k : ℕ) : ℤ := (Nat.choose (n - k) k : ℤ)
  let tr (b : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), t n k * b k
  let wt (b : ℕ → ℤ) (n : ℕ) : ℤ := tr (fun k => (k : ℤ) * b k) n
  let b (k : ℕ) : ℤ := (Nat.choose k (k / 2) : ℤ)
  have t_zero {n k : ℕ} (h : n < 2 * k) : t n k = 0 := by
    unfold t
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    rfl
  have t_pascal (n k : ℕ) : t (n + 2) (k + 1) = t (n + 1) (k + 1) + t n k := by
    by_cases h : k ≤ n
    · unfold t
      rw [show n + 2 - (k + 1) = (n - k) + 1 by omega,
        show n + 1 - (k + 1) = n - k by omega, Nat.choose_succ_succ]
      push_cast
      ring
    · rw [t_zero (by omega), t_zero (by omega), t_zero (by omega)]
      ring
  have t_weight (n k : ℕ) :
      ((n : ℤ) + 1 - 2 * k) * t (n + 1) k = ((n : ℤ) + 1 - k) * t n k := by
    by_cases hk : k ≤ n
    · have h := Nat.choose_mul_succ_eq (n - k) k
      have h' : ((n - k).choose k : ℤ) * ((n - k : ℕ) + 1) =
          (((n - k) + 1).choose k : ℤ) * ((n - k + 1 - k : ℕ) : ℤ) := by
        exact_mod_cast h
      by_cases h2 : 2 * k ≤ n + 1
      · unfold t
        rw [show n + 1 - k = (n - k) + 1 by omega]
        have e1 : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by omega
        have e2 : ((n - k + 1 - k : ℕ) : ℤ) = (n : ℤ) + 1 - 2 * k := by omega
        rw [e1, e2] at h'
        linear_combination -h'
      · rw [t_zero (by omega), t_zero (by omega)]
        ring
    · rw [t_zero (by omega), t_zero (by omega)]
      ring
  have tr_pascal (c : ℕ → ℤ) (n : ℕ) :
      tr c (n + 2) = tr c (n + 1) + tr (fun k => c (k + 1)) n := by
    unfold tr
    rw [sum_range_succ' (fun k => t (n + 2) k * c k) (n + 2),
      sum_range_succ' (fun k => t (n + 1) k * c k) (n + 1)]
    simp_rw [t_pascal, add_mul]
    rw [sum_add_distrib,
      sum_range_succ (fun k => t n k * c (k + 1)) (n + 1),
      show n + 2 = (n + 1) + 1 by omega,
      sum_range_succ (fun k => t (n + 1) (k + 1) * c (k + 1)) (n + 1)]
    rw [t_zero (show n < 2 * (n + 1) by omega),
      t_zero (show n + 1 < 2 * (n + 1 + 1) by omega)]
    simp only [zero_mul, add_zero, t,
      Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    ring
  have tr_extend (c : ℕ → ℤ) (n : ℕ) :
      ∑ k ∈ range (n + 2), t n k * c k = tr c n := by
    rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ]
    simp [t_zero (show n < 2 * (n + 1) by omega), tr]
  have tr_weight (c : ℕ → ℤ) (n : ℕ) :
      ((n : ℤ) + 1) * (tr c (n + 1) - tr c n) =
        2 * wt c (n + 1) - wt c n := by
    have h : (∑ k ∈ range (n + 2), (((n : ℤ) + 1) * (t (n + 1) k * c k) -
          2 * (t (n + 1) k * ((k : ℤ) * c k)))) =
        ∑ k ∈ range (n + 2), (((n : ℤ) + 1) * (t n k * c k) -
          t n k * ((k : ℤ) * c k)) := by
      apply sum_congr rfl
      intro k hk
      linear_combination c k * t_weight n k
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum,
      sum_sub_distrib, ← mul_sum, tr_extend, tr_extend] at h
    change ((n : ℤ) + 1) * tr c (n + 1) - 2 * wt c (n + 1) =
      ((n : ℤ) + 1) * tr c n - wt c n at h
    linear_combination h
  have wt_pascal (c : ℕ → ℤ) (n : ℕ) :
      wt c (n + 2) = wt c (n + 1) + wt (fun k => c (k + 1)) n +
        tr (fun k => c (k + 1)) n := by
    change tr (fun k => (k : ℤ) * c k) (n + 2) = _
    rw [tr_pascal]
    rw [add_assoc (wt c (n + 1))]
    congr 1
    unfold wt tr
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    push_cast
    ring
  have b_even (m : ℕ) : b (2 * m) = (m.centralBinom : ℤ) := by
    simp [b, Nat.centralBinom]
  have b_odd (m : ℕ) : 2 * b (2 * m + 1) = ((m + 1).centralBinom : ℤ) := by
    have h : (2 * m + 2).choose (m + 1) =
        (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) := Nat.choose_succ_succ' _ _
    have hs : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m :=
      Nat.choose_symm_of_eq_add (by omega)
    unfold b Nat.centralBinom
    rw [show (2 * m + 1) / 2 = m by omega, show 2 * (m + 1) = 2 * m + 2 by omega]
    exact_mod_cast (by omega : 2 * (2 * m + 1).choose m = (2 * m + 2).choose (m + 1))
  have b_rec (k : ℕ) :
      ((k : ℤ) + 3) * b (k + 2) = 2 * b (k + 1) + 4 * ((k : ℤ) + 1) * b k := by
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have h : ((m : ℤ) + 1) * ((m + 1).centralBinom : ℤ) =
          2 * (2 * m + 1) * (m.centralBinom : ℤ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ m
      have hodd := b_odd m
      rw [show 2 * m + 2 = 2 * (m + 1) by omega, b_even, b_even]
      push_cast
      linear_combination 2 * h - hodd
    · have h : ((m : ℤ) + 2) * ((m + 2).centralBinom : ℤ) =
          2 * (2 * m + 3) * ((m + 1).centralBinom : ℤ) := by
        have hh := Nat.succ_mul_centralBinom_succ (m + 1)
        exact_mod_cast hh
      have hodd0 := b_odd m
      have hodd1 := b_odd (m + 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega] at hodd1
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, b_even]
      push_cast at hodd1 ⊢
      linear_combination h + ((m : ℤ) + 2) * hodd1 - (4 * ((m : ℤ) + 1)) * hodd0
  have tr_brec (n : ℕ) :
      wt (fun k => b (k + 2)) n + 3 * tr (fun k => b (k + 2)) n =
        2 * tr (fun k => b (k + 1)) n + 4 * wt b n + 4 * tr b n := by
    have h : (∑ k ∈ range (n + 1),
        (t n k * ((k : ℤ) * b (k + 2)) + 3 * (t n k * b (k + 2)))) =
        ∑ k ∈ range (n + 1),
          (2 * (t n k * b (k + 1)) + 4 * (t n k * ((k : ℤ) * b k)) +
            4 * (t n k * b k)) := by
      apply sum_congr rfl
      intro k hk
      linear_combination t n k * b_rec k
    simp only [sum_add_distrib, ← mul_sum] at h
    exact h
  have tr_eliminate (n : ℕ) :
      wt b (n + 4) - 2 * wt b (n + 3) + wt b (n + 2) - 4 * wt b n +
        tr b (n + 4) - 2 * tr b (n + 3) - tr b (n + 2) +
          2 * tr b (n + 1) - 4 * tr b n = 0 := by
    have h := tr_brec n
    have hK2 := wt_pascal b (n + 2)
    have hK1 := wt_pascal b (n + 1)
    have hJ := wt_pascal (fun k => b (k + 1)) n
    have hB := tr_pascal (fun k => b (k + 1)) n
    have hA2 := tr_pascal b (n + 2)
    have hA1 := tr_pascal b (n + 1)
    have hA0 := tr_pascal b n
    simp only [Nat.add_assoc, Nat.reduceAdd] at hK2 hK1 hJ hB hA2 hA1 hA0
    linear_combination h + hK2 - hK1 + hJ + 2 * hB + hA2 - hA1 - 2 * hA0
  have tr_recurrence (n : ℕ) :
      ((n : ℤ) + 6) * tr b (n + 4) - 2 * ((n : ℤ) + 5) * tr b (n + 3) +
        (n : ℤ) * tr b (n + 2) + 2 * tr b (n + 1) -
          4 * ((n : ℤ) + 2) * tr b n = 0 := by
    induction n with
    | zero => norm_num [tr, t, b, Nat.choose, sum_range_succ]
    | succ n ih =>
      have hE0 := tr_eliminate n
      have hE1 := tr_eliminate (n + 1)
      have hF0 := tr_weight b n
      have hF2 := tr_weight b (n + 2)
      have hF3 := tr_weight b (n + 3)
      have hF4 := tr_weight b (n + 4)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hE1 hF2 hF3 hF4 ⊢
      push_cast at hF2 hF3 hF4 ⊢
      linear_combination ih + 2 * hE1 - hE0 - 4 * hF0 + hF2 - 2 * hF3 + hF4
  have tr_eq_a (n : ℕ) : tr b n = (a n : ℤ) := by
    unfold tr a
    push_cast
    symm
    apply sum_subset (by intro k hk; simp only [mem_range] at hk ⊢; omega)
    intro k hk hnot
    change t n k * b k = 0
    rw [t_zero (by simp only [mem_range] at hk hnot; omega)]
    simp
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := tr_recurrence m
  simp_rw [tr_eq_a] at h
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  push_cast
  linear_combination h

end D5.S1.Recurrence.MatharCentralBinomialTransformRecurrence
