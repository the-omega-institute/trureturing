/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdSlope
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdSlope
   mirror-E: none(waiver:quadratic-irrational-family)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.Irrational]
   utility: none
   digest: Explicit radical formulas define the quadratic tail and uniform minority frequency. -/

import Mathlib.NumberTheory.Real.Irrational
import D5.S1.Words.BalancedThreshold.BalancedThresholdBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

/-- The positive root for the alternating continued-fraction tail. -/
noncomputable def quadraticTail (t : ℕ) : ℝ :=
  let N := (t - 2) * (t + 1)
  (Real.sqrt (N * (N + 4) : ℕ) - N) / (2 * (t - 2 : ℕ))

/-- The minority frequency in the uniform odd-alphabet construction. -/
noncomputable def uniformSlope (t : ℕ) : ℝ :=
  1 / ((t : ℝ) + 3 + 1 / ((t : ℝ) + quadraticTail t))


end D5.S1.Words.BalancedThreshold
