/- GID: D5/S3/ArithSums/MatharA386830
   generality: I
   mirror-B: D5/B/S3/ArithSums/MatharA386830
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Literal binomial sum and ordinary differential recurrence for OEIS A386830. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace D5.S3.ArithSums.MatharA386830
open scoped BigOperators
open Finset

/-- The inclusive integer NAME sum in OEIS A386830. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (3 : ℤ)^k * 2^(n-k) *
    ((3*n+1).choose k : ℤ) * ((3*n-k).choose (n-k) : ℤ)

private def t (n : ℕ) : ℤ :=
  ∑ j ∈ range (n+1), (5 : ℤ)^j * (-2)^(n-j) * ((3*n+1).choose j : ℤ)

private theorem signed_partial (N M : ℕ) :
    (∑ r ∈ range (M+1), (-1 : ℤ)^(M-r) * ((N+1).choose r : ℤ)) =
      (N.choose M : ℤ) := by
  have hp (r : ℕ) (hr : r ≤ M) : (-1 : ℤ)^(M-r) = (-1)^M * (-1)^r := by
    have hsq : ((-1 : ℤ)^r)^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
      norm_num
    calc
      (-1 : ℤ)^(M-r) = (-1)^(M-r) * ((-1)^r)^2 := by rw [hsq, mul_one]
      _ = (-1)^M * (-1)^r := by
        rw [pow_two, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hr]
  calc
    _ = (-1 : ℤ)^M * ∑ r ∈ range (M+1), (-1)^r * ((N+1).choose r : ℤ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      rw [hp r (by simpa using mem_range.mp hr)]
      ring
    _ = _ := by
      rw [Int.alternating_sum_range_choose_eq_choose, ← mul_assoc, ← pow_two,
        ← pow_mul, Nat.mul_comm M 2, pow_mul]
      norm_num

private theorem literal_eq_transform (n : ℕ) : a n = t n := by
  have expand : t n = ∑ j ∈ range (n+1), ∑ k ∈ range (j+1),
      (3 : ℤ)^k * 2^(n-k) * (-1)^(n-j) *
        ((3*n+1).choose j : ℤ) * (j.choose k : ℤ) := by
    unfold t
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using mem_range.mp hj
    rw [show (5 : ℤ) = 3+2 by norm_num, add_pow, sum_mul, sum_mul]
    apply sum_congr rfl
    intro k hk
    have hkj : k ≤ j := by simpa using mem_range.mp hk
    have hp : (2 : ℤ)^(j-k) * 2^(n-j) = 2^(n-k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [show (-2 : ℤ) = (-1)*2 by norm_num, mul_pow]
    calc
      _ = (3 : ℤ)^k * (2^(j-k) * 2^(n-j)) * (-1)^(n-j) *
          ((3*n+1).choose j : ℤ) * (j.choose k : ℤ) := by ring
      _ = _ := by rw [hp]
  have swap := sum_Ico_Ico_comm 0 (n+1)
    (fun k j => (3 : ℤ)^k * 2^(n-k) * (-1)^(n-j) *
      ((3*n+1).choose j : ℤ) * (j.choose k : ℤ))
  simp only [← range_eq_Ico] at swap
  rw [expand, ← swap]
  unfold a
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using mem_range.mp hk
  have inner : (∑ j ∈ Ico k (n+1), (-1 : ℤ)^(n-j) *
      (((3*n+1).choose j : ℤ) * (j.choose k : ℤ))) =
        ((3*n+1).choose k : ℤ) * ((3*n-k).choose (n-k) : ℤ) := by
    calc
      _ = ∑ j ∈ Ico k (n+1), (-1 : ℤ)^(n-j) *
          (((3*n+1).choose k : ℤ) * ((3*n+1-k).choose (j-k) : ℤ)) := by
        apply sum_congr rfl
        intro j hj
        rw [← Nat.cast_mul, Nat.choose_mul (mem_Ico.mp hj).1, Nat.cast_mul]
      _ = ((3*n+1).choose k : ℤ) * ∑ r ∈ range (n-k+1),
          (-1 : ℤ)^(n-k-r) * ((3*n-k+1).choose r : ℤ) := by
        rw [sum_Ico_eq_sum_range, show n+1-k = n-k+1 by omega, mul_sum]
        apply sum_congr rfl
        intro r hr
        rw [show n-(k+r) = n-k-r by omega, show k+r-k = r by omega,
          show 3*n+1-k = 3*n-k+1 by omega]
        ring
      _ = _ := by rw [signed_partial]
  calc
    _ = (3 : ℤ)^k * 2^(n-k) *
        (((3*n+1).choose k : ℤ) * ((3*n-k).choose (n-k) : ℤ)) := by ring
    _ = _ := by
      rw [← inner, mul_sum]
      apply sum_congr rfl
      intro j hj
      ring

end D5.S3.ArithSums.MatharA386830
