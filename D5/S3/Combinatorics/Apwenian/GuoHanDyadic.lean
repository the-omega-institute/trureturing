/- GID: D5/S3/Combinatorics/Apwenian/GuoHanDyadic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apwenian/GuoHanDyadic
   mirror-E: none(waiver:dyadic-tree-expansion)
   anchors: []
   utility: none
   digest: Expanding the binary recursion gives the sum over every dyadic descendant interval. -/

import D5.S3.Combinatorics.Apwenian.GuoHanBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Apwenian.GuoHan

open scoped BigOperators

/-- Binary descendants partition a consecutive interval at every depth. -/
theorem dyadic_expansion (b : ℕ → ZMod 2)
    (hrec : ∀ n, b n = b (2 * n + 1) + b (2 * n + 2)) (h n : ℕ) :
    b n = ∑ j ∈ Finset.range (2 ^ h), b (2 ^ h * (n + 1) - 1 + j) := by
  have hpairs (f : ℕ → ZMod 2) (k : ℕ) :
      (∑ j ∈ Finset.range (2 * k), f j) =
        ∑ j ∈ Finset.range k, (f (2 * j) + f (2 * j + 1)) := by
    induction k with
    | zero => simp only [mul_zero, Finset.sum_range_zero]
    | succ k ih =>
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
          Finset.sum_range_succ, add_assoc]
  induction h with
  | zero => simp
  | succ h ih =>
      have hpos : 0 < 2 ^ h := pow_pos (by omega) _
      have hstart : 1 ≤ 2 ^ h * (n + 1) := by nlinarith
      rw [pow_succ, mul_comm (2 ^ h) 2, hpairs]
      rw [ih]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hrec]
      have haddr : 2 * (2 ^ h * (n + 1) - 1 + j) + 1 =
          2 * 2 ^ h * (n + 1) - 1 + 2 * j := by
        have he : 2 * 2 ^ h * (n + 1) = 2 * (2 ^ h * (n + 1)) := by ring
        omega
      rw [haddr]
      congr 1
      apply congrArg b
      have he : 2 * 2 ^ h * (n + 1) = 2 * (2 ^ h * (n + 1)) := by ring
      omega

end D5.S3.Combinatorics.Apwenian.GuoHan
