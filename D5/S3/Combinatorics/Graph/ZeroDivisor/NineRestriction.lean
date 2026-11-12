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

end D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction
