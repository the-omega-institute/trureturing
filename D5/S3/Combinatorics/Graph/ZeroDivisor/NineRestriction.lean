/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction
   mirror-E: none(waiver:uniform-binomial-sampling)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Vandermonde]
   utility: none
   digest: Nine-element restriction gives uniform marked-prefix and unmarked-pair bounds. -/

import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction

open Finset

/-- Count a nine-subset together with a marked prefix and an unmarked pair. -/
theorem nine_restriction_count (m n k : ℕ) (hk : 3 ≤ k ∧ k ≤ 5) :
    (∑ j ∈ range 10,
      m.choose j * n.choose (9-j) * j.choose (k-1) * (9-j).choose 2) =
      m.choose (k-1) * n.choose 2 * (m+n-(k+1)).choose (9-(k+1)) := by
  let a := k-1
  let r := 9-(k+1)
  have ha : 2 ≤ a ∧ a ≤ 4 := by dsimp [a]; omega
  have hr : 8-a = r+1 := by dsimp [a, r]; omega
  have hsub : Ico a 8 ⊆ range 10 := by
    intro j hj
    simp only [mem_Ico, mem_range] at *
    omega
  have hvanish : ∀ j ∈ range 10, j ∉ Ico a 8 →
      m.choose j * n.choose (9-j) * j.choose a * (9-j).choose 2 = 0 := by
    intro j hj hnot
    by_cases hja : j < a
    · simp [Nat.choose_eq_zero_of_lt hja]
    · have hlast : 9-j < 2 := by
        simp only [mem_Ico, not_and, not_lt] at hnot
        omega
      simp [Nat.choose_eq_zero_of_lt hlast]
  have key : (∑ j ∈ range 10,
      m.choose j * n.choose (9-j) * j.choose a * (9-j).choose 2) =
      m.choose a * n.choose 2 * ((m-a)+(n-2)).choose r := by
    calc
      _ = ∑ t ∈ range (r+1),
          m.choose (a+t) * n.choose (9-(a+t)) *
            (a+t).choose a * (9-(a+t)).choose 2 := by
        rw [← sum_subset hsub hvanish, sum_Ico_eq_sum_range, hr]
      _ = m.choose a * n.choose 2 *
          ∑ t ∈ range (r+1), (m-a).choose t * (n-2).choose (r-t) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro t ht
        have ht' := mem_range.mp ht
        have htwo : 2 ≤ 9-(a+t) := by dsimp [a, r] at *; omega
        have heq : 9-(a+t)-2 = r-t := by dsimp [a, r]; omega
        calc
          _ = (m.choose (a+t) * (a+t).choose a) *
              (n.choose (9-(a+t)) * (9-(a+t)).choose 2) := by ring
          _ = _ := by
            rw [Nat.choose_mul (Nat.le_add_right a t), Nat.choose_mul htwo,
              Nat.add_sub_cancel_left, heq]
            ring
      _ = _ := by
        rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ j ∈ range 10,
    m.choose j * n.choose (9-j) * j.choose a * (9-j).choose 2) = _
  rw [key]
  by_cases hm : a ≤ m
  · by_cases hn : 2 ≤ n
    · have heq : (m-a)+(n-2) = m+n-(k+1) := by dsimp [a] at *; omega
      rw [heq]
    · simp [Nat.choose_eq_zero_of_lt (by omega : n < 2)]
  · have hz : m.choose a = 0 := Nat.choose_eq_zero_of_lt (by omega)
    change m.choose a * n.choose 2 * _ = m.choose a * n.choose 2 * _
    simp [hz]

/-- Uniform restriction to a nine-subset, with rational hypergeometric weights. -/
theorem nine_restriction (N m k : ℕ) (hN : 9 ≤ N) (hm : m ≤ N)
    (hk : 3 ≤ k ∧ k ≤ 5) :
    (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) /
        ((N.choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) =
      ∑ j ∈ range 10,
        ((m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) / (N.choose 9 : ℚ)) *
          ((j.choose (k-1) : ℚ) * ((9-j).choose 2 : ℚ) /
            ((9 : ℕ).choose (k+1) * ((k+1).choose 2 : ℚ))) := by
  have hmn : m+(N-m) = N := by omega
  have hcount := nine_restriction_count m (N-m) k hk
  rw [hmn] at hcount
  have hsum : (∑ j ∈ range 10,
      (m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) *
        (j.choose (k-1) : ℚ) * ((9-j).choose 2 : ℚ)) =
      (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) *
        ((N-(k+1)).choose (9-(k+1)) : ℚ) := by exact_mod_cast hcount
  have hcomp : (N.choose 9 : ℚ) * ((9 : ℕ).choose (k+1) : ℚ) =
      (N.choose (k+1) : ℚ) * ((N-(k+1)).choose (9-(k+1)) : ℚ) := by
    exact_mod_cast (Nat.choose_mul (n := N) (k := 9) (s := k+1) (by omega))
  have hD : (N.choose (k+1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : k+1 ≤ N)
  have hW : (N.choose 9 : ℚ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hN
  have hS : ((9 : ℕ).choose (k+1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : k+1 ≤ 9)
  have hP : ((k+1).choose 2 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : 2 ≤ k+1)
  calc
    _ = ((m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) *
          ((N-(k+1)).choose (9-(k+1)) : ℚ)) /
        ((N.choose 9 : ℚ) * ((9 : ℕ).choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) := by
      apply (div_eq_div_iff (mul_ne_zero hD hP)
        (mul_ne_zero (mul_ne_zero hW hS) hP)).mpr
      linear_combination (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) *
        ((k+1).choose 2 : ℚ) * hcomp
    _ = (∑ j ∈ range 10,
        (m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) *
          (j.choose (k-1) : ℚ) * ((9-j).choose 2 : ℚ)) /
        ((N.choose 9 : ℚ) * ((9 : ℕ).choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) := by
      rw [hsum]
    _ = _ := by
      rw [sum_div]
      apply sum_congr rfl
      intro j _
      field_simp
      <;> ring

/-- The three small-rank bounds hold in every population of size at least nine. -/
theorem nine_restriction_bound (N m k : ℕ) (hN : 9 ≤ N) (hm : m ≤ N)
    (hk : 3 ≤ k ∧ k ≤ 5) :
    (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) /
        ((N.choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) ≤
      if k = 3 then (5/63 : ℚ) else if k = 4 then (1/21 : ℚ) else (1/28 : ℚ) := by
  have hmn : m+(N-m) = N := by omega
  have hW : (N.choose 9 : ℚ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hN
  have hv : ∑ j ∈ range 10, m.choose j * (N-m).choose (9-j) = N.choose 9 := by
    have h := Nat.add_choose_eq m (N-m) 9
    rw [hmn, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    exact h.symm
  have hw : (∑ j ∈ range 10,
      (m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) / (N.choose 9 : ℚ)) = 1 := by
    rw [← sum_div]
    have hv' : (∑ j ∈ range 10,
        (m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ)) = (N.choose 9 : ℚ) := by
      exact_mod_cast hv
    rw [hv', div_self hW]
  have htable : ∀ j ∈ range 10,
      (j.choose (k-1) : ℚ) * ((9-j).choose 2 : ℚ) /
          (((9 : ℕ).choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) ≤
        if k = 3 then (5/63 : ℚ) else if k = 4 then (1/21 : ℚ) else (1/28 : ℚ) := by
    intro j hj
    have hj' := mem_range.mp hj
    obtain ⟨hklo, hkhi⟩ := hk
    interval_cases k <;> interval_cases j <;> norm_num [Nat.choose]
  rw [nine_restriction N m k hN hm hk]
  calc
    _ ≤ ∑ j ∈ range 10,
        ((m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) / (N.choose 9 : ℚ)) *
          (if k = 3 then (5/63 : ℚ) else if k = 4 then (1/21 : ℚ) else (1/28 : ℚ)) := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (htable j hj) (by positivity)
    _ = _ := by rw [← sum_mul, hw, one_mul]

end D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction
