/- GID: D5/S3/Arith/FibonacciAtomic/WeightedInghamRateDraft
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/WeightedInghamRateDraft
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact Fibonacci remainders in the main segment of a weighted fractional-part sum. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.WeightedInghamRate

example (a : ℤ) (j : ℕ) :
    Int.fib (a + j) + (-1 : ℤ) ^ j * Int.fib (a - j) =
      (Int.fib ((j : ℤ) - 1) + Int.fib ((j : ℤ) + 1)) * Int.fib a := by
  have hp := Int.fib_add (j : ℤ) a
  have hm := Int.fib_add (-(j : ℤ)) a
  rw [show -(j : ℤ) - 1 = -((j + 1 : ℕ) : ℤ) by omega,
    Int.fib_neg_natCast, Int.fib_neg_natCast] at hm
  rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega, Int.fib_natCast]
  simp only [pow_add, pow_one, Int.fib_natCast] at hp hm
  rw [add_comm] at hp
  rw [show -(j : ℤ) + a = a - j by ring] at hm
  rcases Nat.even_or_odd j with he | ho
  · rw [he.neg_one_pow] at hm ⊢
    rw [hp, hm]
    ring
  · rw [ho.neg_one_pow] at hm ⊢
    rw [hp, hm]
    ring

example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (b / a) * (⌊1 / (b / a)⌋ : ℝ) =
      1 - (b / a) * Int.fract (a / b) := by
  rw [one_div_div, Int.fract]
  field_simp
  ring

end D5.S3.Arith.FibonacciAtomic.WeightedInghamRate
