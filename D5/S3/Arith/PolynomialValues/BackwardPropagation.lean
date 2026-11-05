/- GID: D5/S3/Arith/PolynomialValues/BackwardPropagation
   generality: G
   mirror-B: D5/B/S3/Arith/PolynomialValues/BackwardPropagation
   mirror-E: none(waiver:polynomial-additive-subgroup-propagation)
   anchors: [mathlib/module/Mathlib.Algebra.Group.ForwardDiff]
   utility: none
   digest: Polynomial values in an additive subgroup at every natural input remain there at every integer input. -/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PolynomialValues.BackwardPropagation

open Finset

/-- Membership of polynomial values in an additive subgroup propagates from
all nonnegative integers to all integers. No closure under division or
multiplication is required of the subgroup. -/
theorem eval_int_mem_of_eval_nat_mem (H : AddSubgroup ℚ) (p : Polynomial ℚ)
    (h : ∀ m : ℕ, p.eval (m : ℚ) ∈ H) :
    ∀ z : ℤ, p.eval (z : ℚ) ∈ H := by
  classical
  let d := p.natDegree + 1
  have annihilate (x : ℚ) :
      ∑ k ∈ range (d + 1),
        ((-1 : ℤ) ^ (d - k) * (d.choose k : ℤ)) • p.eval (x + k) = 0 := by
    have hz := congrFun (p.fwdDiff_iter_degree_add_one_eq_zero) x
    rw [fwdDiff_iter_eq_sum_shift] at hz
    simpa [d, nsmul_eq_mul] using hz
  have backward : ∀ t : ℕ, p.eval (-(t : ℚ)) ∈ H := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      by_cases ht : t = 0
      · subst t
        simpa using h 0
      have shifted (k : ℕ) (hk : k < d) :
          p.eval (-(t : ℚ) + (k + 1 : ℕ)) ∈ H := by
        by_cases hkt : k + 1 ≤ t
        · have he : -(t : ℚ) + (k + 1 : ℕ) = -((t - (k + 1) : ℕ) : ℚ) := by
            rw [Nat.cast_sub hkt]
            push_cast
            ring
          rw [he]
          exact ih (t - (k + 1)) (by omega)
        · have he : -(t : ℚ) + (k + 1 : ℕ) = ((k + 1 - t : ℕ) : ℚ) := by
            rw [Nat.cast_sub (by omega : t ≤ k + 1)]
            push_cast
            ring
          rw [he]
          exact h _
      have hs : (∑ k ∈ range d,
          ((-1 : ℤ) ^ (d - (k + 1)) * (d.choose (k + 1) : ℤ)) •
            p.eval (-(t : ℚ) + (k + 1 : ℕ))) ∈ H := by
        apply H.sum_mem
        intro k hk
        exact H.zsmul_mem (shifted k (mem_range.mp hk)) _
      have hz := annihilate (-(t : ℚ))
      rw [sum_range_succ'] at hz
      simp only [Nat.sub_zero, Nat.choose_zero_right, Int.natCast_one,
        mul_one, Nat.cast_zero, add_zero] at hz
      have hm : ((-1 : ℤ) ^ d) • p.eval (-(t : ℚ)) ∈ H := by
        have he : ((-1 : ℤ) ^ d) • p.eval (-(t : ℚ)) =
            -(∑ k ∈ range d,
              ((-1 : ℤ) ^ (d - (k + 1)) * (d.choose (k + 1) : ℤ)) •
                p.eval (-(t : ℚ) + (k + 1 : ℕ))) := by
          exact eq_neg_of_add_eq_zero_right hz
        rw [he]
        exact H.neg_mem hs
      have hinv := H.zsmul_mem hm ((-1 : ℤ) ^ d)
      have sq : ((-1 : ℤ) ^ d) * ((-1 : ℤ) ^ d) = 1 := by
        rw [← mul_pow]
        simp
      simpa only [smul_smul, sq, one_smul] using hinv
  intro z
  cases z with
  | ofNat m => simpa using h m
  | negSucc m => simpa only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev,
      add_comm] using backward (m + 1)

end D5.S3.Arith.PolynomialValues.BackwardPropagation
