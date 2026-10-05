/- GID: D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/UnitShiftNormBudget
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual coordinate gcd normalization gives cubic shift costs and joint growth budgets. -/

import D5.S1.Scale.Fibonacci
import D5.S1.Scale.Embedding
import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.UnitShiftNormBudget

open D5.S0.Carrier
open D5.S1.Scale
open GraftAffineClosure (quantity)

local notation "φ" => Real.goldenRatio
local notation "ψ" => Real.goldenConj

/-- Absorb the unit bit and translate along the kernel of the quantity. -/
def shiftedComposition (j g : ℕ) (r : ℤ) : GoldenInt :=
  ⟨g * (Nat.fib (j - 1) : ℤ) + 3 * r - 1,
    g * (Nat.fib j : ℤ) + 1 - 2 * r⟩

/-- The source quantity includes its unit bit. -/
def sourceQuantity (j g : ℕ) : ℕ :=
  g * quantity (Nat.fib (j - 1), Nat.fib j) + 1

/-- Divide the source quantity by the actual gcd of the translated coordinates. -/
noncomputable def primitiveQuantity (j g : ℕ) (r : ℤ) : ℝ :=
  sourceQuantity j g / (Int.gcd (shiftedComposition j g r).a
    (shiftedComposition j g r).b : ℝ)

/-- Normalize the actual golden norm by the square of the coordinate gcd. -/
noncomputable def primitiveNorm (j g : ℕ) (r : ℤ) : ℝ :=
  |(norm (shiftedComposition j g r) : ℝ)| /
    (Int.gcd (shiftedComposition j g r).a (shiftedComposition j g r).b : ℝ) ^ 2

private theorem polynomial_ne_zero (g r s : ℤ) (hg : 2 ≤ g)
    (hs : s = 1 ∨ s = -1) : r ^ 2 - 3 * r + 1 + g ^ 2 * s ≠ 0 := by
  intro hz
  rcases hs with rfl | rfl
  · nlinarith [sq_nonneg (2 * r - 3), sq_nonneg (g - 2)]
  · have hlo : 2 * g < |2 * r - 3| := by
      nlinarith [sq_abs (2 * r - 3), abs_nonneg (2 * r - 3)]
    have hhi : |2 * r - 3| < 2 * g + 1 := by
      nlinarith [sq_abs (2 * r - 3), abs_nonneg (2 * r - 3)]
    omega

end D5.S3.Arith.FibonacciAtomic.UnitShiftNormBudget
