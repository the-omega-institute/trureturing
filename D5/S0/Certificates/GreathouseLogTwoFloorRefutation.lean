/- GID: D5/S0/Certificates/GreathouseLogTwoFloorRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/GreathouseLogTwoFloorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Floor.Semiring, mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/GreathouseLogTwoFloorRefutation.claim; result=D5/S0/Certificates/GreathouseLogTwoFloorRefutation.result; claim=D5/S0/Certificates/GreathouseLogTwoFloorRefutation.claim
   digest: The index 1121626023352383 refutes Greathouse's floor formula for OEIS A175406. -/

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.GreathouseLogTwoFloorRefutation

/-!
OEIS A175406 asks for the greatest natural number `k` such that
`(1 + 1 / n) ^ k <= 2`.  Charles R. Greathouse IV conjectured in 2012 that
this value is always `floor ((n + 1 / 2) * log 2)`.

The definition below is literal.  For positive `n` its defining set is
nonempty and bounded above.  As usual for the conditionally complete order
on the natural numbers, `sSup` is zero when its argument is unbounded.
-/

/-- The greatest exponent whose `n`-th harmonic perturbation stays at most two. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | (1 + 1 / (n : ℝ)) ^ k ≤ 2}

/-- Greathouse's conjectured closed formula for OEIS A175406. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n = ⌊((n : ℝ) + 1 / 2) * Real.log 2⌋₊

example :
    (∑ k ∈ Finset.range 36,
        (2 : ℝ) * (1 / (2 * k + 1)) * (1 / 3) ^ (2 * k + 1)) ≤ Real.log 2 := by
  let f : ℕ → ℝ := fun k =>
    2 * (1 / (2 * k + 1)) * (1 / 3) ^ (2 * k + 1)
  have hlog : HasSum f (Real.log 2) := by
    convert! Real.hasSum_log_one_add_inv (a := (1 : ℝ)) (by norm_num) using 1 <;>
      norm_num [f]
  have hpartial := hlog.summable.sum_le_tsum (Finset.range 36) (fun k _ => by
    dsimp [f]
    positivity)
  rw [hlog.tsum_eq] at hpartial
  exact hpartial

#print axioms a
#print axioms claim

end D5.S0.Certificates.GreathouseLogTwoFloorRefutation
