/- GID: D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion
   generality: G
   mirror-B: D5/B/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Schulte's conjectured A008287 quadrinomial alternating-binomial expansion. -/

import Mathlib.Algebra.Polynomial.Coeff

namespace D5.S1.Recurrence.SchulteQuadrinomialAlternatingBinomialExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial

/-- A008287: the coefficient of `x^k` in `(1+x+x²+x³)^n`. -/
noncomputable def T (n k : ℕ) : ℤ :=
  ((1 + X + X ^ 2 + X ^ 3 : ℤ[X]) ^ n).coeff k

/-- Schulte's alternating-binomial expansion of the quadrinomial coefficients. -/
theorem result (n k : ℕ) (_hk : k ≤ 3 * n) :
    T n k = ∑ j ∈ Finset.range (k + 1),
      (-2 : ℤ) ^ j * (n.choose j : ℤ) *
        ((3 * n - 2 * j).choose (k - j) : ℤ) := by
  have hfactor : (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) =
      ((-2 : ℤ[X]) * X) * (1 + X) + (1 + X) ^ 3 := by ring
  have hpoly : (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        (((-2 : ℤ[X]) * X) * (1 + X)) ^ j *
        ((1 + X) ^ 3) ^ (n - j) * (n.choose j : ℤ[X]) := by
    rw [hfactor, add_pow]
  have hterm (j : ℕ) (hj : j ≤ n) :
      (((-2 : ℤ[X]) * X) * (1 + X)) ^ j *
        ((1 + X) ^ 3) ^ (n - j) * (n.choose j : ℤ[X]) =
      C ((-2 : ℤ) ^ j * (n.choose j : ℤ)) * X ^ j *
        (1 + X) ^ (3 * n - 2 * j) := by
    have he : 3 * n - 2 * j = j + 3 * (n - j) := by omega
    calc
      _ = ((-2 : ℤ[X]) ^ j) * X ^ j *
          (1 + X) ^ (j + 3 * (n - j)) * (n.choose j : ℤ[X]) := by
        rw [← pow_mul]
        simp only [mul_pow]
        ring
      _ = _ := by
        rw [← he]
        have hcast : (-2 : ℤ[X]) ^ j = C ((-2 : ℤ) ^ j) := by simp
        have hncast : (n.choose j : ℤ[X]) = C (n.choose j : ℤ) := by simp
        rw [hcast, hncast, map_mul]
        ring
  let f : ℕ → ℤ := fun j => (-2 : ℤ) ^ j * (n.choose j : ℤ) *
    ((3 * n - 2 * j).choose (k - j) : ℤ)
  have hcoeff (j : ℕ) :
      (C ((-2 : ℤ) ^ j * (n.choose j : ℤ)) * X ^ j *
        (1 + X) ^ (3 * n - 2 * j)).coeff k =
      if j ≤ k then f j else 0 := by
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    by_cases hjk : j ≤ k
    · simp only [if_pos hjk, coeff_one_add_X_pow]
      rfl
    · simp only [if_neg hjk, mul_zero]
  have hindex :
      (∑ j ∈ Finset.range (n + 1), if j ≤ k then f j else 0) =
      ∑ j ∈ Finset.range (k + 1), f j := by
    let m : ℕ := max n k + 1
    have hnsub : Finset.range (n + 1) ⊆ Finset.range m := by
      change Finset.range (n + 1) ⊆ Finset.range (max n k + 1)
      exact Finset.range_mono (Nat.add_le_add_right (Nat.le_max_left n k) 1)
    have hksub : Finset.range (k + 1) ⊆ Finset.range m := by
      change Finset.range (k + 1) ⊆ Finset.range (max n k + 1)
      exact Finset.range_mono (Nat.add_le_add_right (Nat.le_max_right n k) 1)
    have hleft :
        (∑ j ∈ Finset.range (n + 1), if j ≤ k then f j else 0) =
        ∑ j ∈ Finset.range m, if j ≤ k then f j else 0 := by
      apply Finset.sum_subset hnsub
      intro j hjm hjnot
      have hnj : n < j := by
        simp only [Finset.mem_range, not_lt] at hjnot
        omega
      simp [f, Nat.choose_eq_zero_of_lt hnj]
    have hright :
        (∑ j ∈ Finset.range (k + 1), f j) =
        ∑ j ∈ Finset.range m, if j ≤ k then f j else 0 := by
      calc
        (∑ j ∈ Finset.range (k + 1), f j) =
            ∑ j ∈ Finset.range (k + 1), if j ≤ k then f j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_pos (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)]
        _ = ∑ j ∈ Finset.range m, if j ≤ k then f j else 0 := by
          apply Finset.sum_subset hksub
          intro j hjm hjnot
          have hjk : ¬ j ≤ k := by
            simp only [Finset.mem_range, not_lt] at hjnot
            omega
          rw [if_neg hjk]
    exact hleft.trans hright.symm
  calc
    T n k = ∑ j ∈ Finset.range (n + 1),
        (C ((-2 : ℤ) ^ j * (n.choose j : ℤ)) * X ^ j *
          (1 + X) ^ (3 * n - 2 * j)).coeff k := by
      rw [T, hpoly, finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro j hj
      apply congrArg (fun p : ℤ[X] => p.coeff k)
      exact hterm j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)
    _ = ∑ j ∈ Finset.range (n + 1), if j ≤ k then f j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hcoeff j
    _ = ∑ j ∈ Finset.range (k + 1), f j := hindex
    _ = ∑ j ∈ Finset.range (k + 1), (-2 : ℤ) ^ j * (n.choose j : ℤ) *
        ((3 * n - 2 * j).choose (k - j) : ℤ) := rfl

end D5.S1.Recurrence.SchulteQuadrinomialAlternatingBinomialExpansion
