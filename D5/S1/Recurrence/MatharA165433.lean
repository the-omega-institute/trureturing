/- GID: D5/S1/Recurrence/MatharA165433
   generality: G
   mirror-B: D5/B/S1/Recurrence/MatharA165433
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rational binomial sum and Mathar recurrence for OEIS A165433. -/

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

namespace D5.S1.Recurrence.MatharA165433
open Finset

def a (n : ℕ) : ℚ :=
  ∑ k ∈ range (n / 2 + 1), (Nat.choose (n - k) k : ℚ) *
    ((2 * k).factorial : ℚ) / ((k.factorial : ℚ) * 2 ^ k)

def claim : Prop := ∀ n : ℕ, 3 ≤ n →
  2 * a n - 3 * a (n - 1) + (3 - 2 * (n : ℚ)) * a (n - 2) +
    (2 * (n : ℚ) - 3) * a (n - 3) = 0

theorem result : claim := by
  let t (n k : ℕ) : ℚ := (Nat.choose (n - k) k : ℚ)
  let tr (b : ℕ → ℚ) (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), t n k * b k
  let wt (b : ℕ → ℚ) (n : ℕ) : ℚ := tr (fun k => (k : ℚ) * b k) n
  let b (k : ℕ) : ℚ := ((2 * k).factorial : ℚ) / ((k.factorial : ℚ) * 2 ^ k)
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
      ((n : ℚ) + 1 - 2 * k) * t (n + 1) k = ((n : ℚ) + 1 - k) * t n k := by
    by_cases hk : k ≤ n
    · have h := Nat.choose_mul_succ_eq (n - k) k
      have h' : ((n - k).choose k : ℚ) * ((n - k : ℕ) + 1) =
          (((n - k) + 1).choose k : ℚ) * ((n - k + 1 - k : ℕ) : ℚ) := by
        exact_mod_cast h
      by_cases h2 : 2 * k ≤ n + 1
      · unfold t
        rw [show n + 1 - k = (n - k) + 1 by omega]
        have e1 : ((n - k : ℕ) : ℚ) = (n : ℚ) - k := by omega
        have e2 : ((n - k + 1 - k : ℕ) : ℚ) = (n : ℚ) + 1 - 2 * k := by omega
        rw [e1, e2] at h'
        linear_combination -h'
      · rw [t_zero (by omega), t_zero (by omega)]
        ring
    · rw [t_zero (by omega), t_zero (by omega)]
      ring
  have tr_pascal (c : ℕ → ℚ) (n : ℕ) :
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
  have tr_extend (c : ℕ → ℚ) (n : ℕ) :
      ∑ k ∈ range (n + 2), t n k * c k = tr c n := by
    rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ]
    simp [t_zero (show n < 2 * (n + 1) by omega), tr]
  have tr_weight (c : ℕ → ℚ) (n : ℕ) :
      ((n : ℚ) + 1) * (tr c (n + 1) - tr c n) =
        2 * wt c (n + 1) - wt c n := by
    have h : (∑ k ∈ range (n + 2), (((n : ℚ) + 1) * (t (n + 1) k * c k) -
          2 * (t (n + 1) k * ((k : ℚ) * c k)))) =
        ∑ k ∈ range (n + 2), (((n : ℚ) + 1) * (t n k * c k) -
          t n k * ((k : ℚ) * c k)) := by
      apply sum_congr rfl
      intro k hk
      linear_combination c k * t_weight n k
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum,
      sum_sub_distrib, ← mul_sum, tr_extend, tr_extend] at h
    change ((n : ℚ) + 1) * tr c (n + 1) - 2 * wt c (n + 1) =
      ((n : ℚ) + 1) * tr c n - wt c n at h
    linear_combination h
  have wt_pascal (c : ℕ → ℚ) (n : ℕ) :
      wt c (n + 2) = wt c (n + 1) + wt (fun k => c (k + 1)) n +
        tr (fun k => c (k + 1)) n := by
    change tr (fun k => (k : ℚ) * c k) (n + 2) = _
    rw [tr_pascal]
    rw [add_assoc (wt c (n + 1))]
    congr 1
    unfold wt tr
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    push_cast
    ring
  have b_rec (k : ℕ) : b (k + 1) = (2 * (k : ℚ) + 1) * b k := by
    have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hp : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    dsimp [b]
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    <;> ring
  have tr_brec (n : ℕ) : tr (fun k => b (k + 1)) n = 2 * wt b n + tr b n := by
    unfold tr wt
    simp_rw [b_rec]
    rw [← mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    ring
  have tr_rec (n : ℕ) :
      2 * tr b (n + 3) - 3 * tr b (n + 2) +
        (3 - 2 * ((n : ℚ) + 3)) * tr b (n + 1) +
        (2 * ((n : ℚ) + 3) - 3) * tr b n = 0 := by
    have h0 := tr_pascal b n
    have h1 := tr_pascal b (n + 1)
    have h2 := tr_brec n
    have h3 := tr_brec (n + 1)
    have h4 := tr_weight b n
    simp only [Nat.add_assoc, Nat.reduceAdd] at h1
    linear_combination 2 * h1 - h0 + 2 * h3 - h2 + 2 * h4
  have tr_eq_a (n : ℕ) : tr b n = a n := by
    unfold tr a
    simp only [mul_div_assoc]
    symm
    apply sum_subset (by intro k hk; simp only [mem_range] at hk ⊢; omega)
    intro k hk hnot
    change t n k * b k = 0
    rw [t_zero (by simp only [mem_range] at hk hnot; omega)]
    simp
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := tr_rec m
  simp_rw [tr_eq_a] at h
  simpa only [Nat.add_sub_cancel, show m + 3 - 1 = m + 2 by omega,
    show m + 3 - 2 = m + 1 by omega, Nat.cast_add, Nat.cast_ofNat] using h

end D5.S1.Recurrence.MatharA165433
