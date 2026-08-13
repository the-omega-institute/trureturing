/- GID: D5/S1/Deficit/GoldenDeficitCoin
   generality: I
   mirror-B: D5/B/S1/Deficit/GoldenDeficitCoin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden quadratic law gives an exact unit deficit. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Deficit.GoldenDeficitCoin

/-- Twice the square of the real golden ratio exceeds its cube by exactly one.

This is an honest partial closure of only the algebraic identity in the source proposition. It does
not assert the critical-line pullback, the structural zero-line interpretation, the slope formula,
or any numerical window certificate. -/
theorem golden_deficit_coin_identity :
    2 * Real.goldenRatio ^ 2 - Real.goldenRatio ^ 3 = 1 := by
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
    Real.goldenRatio_sq
  have hcube : Real.goldenRatio ^ 3 =
      (Real.goldenRatio + 1) * Real.goldenRatio := by
    calc
      Real.goldenRatio ^ 3 = Real.goldenRatio ^ 2 * Real.goldenRatio := by
        simpa using pow_succ Real.goldenRatio 2
      _ = (Real.goldenRatio + 1) * Real.goldenRatio := by rw [hsq]
  rw [hsq, hcube]
  nlinarith [hsq]

end D5.S1.Deficit.GoldenDeficitCoin
