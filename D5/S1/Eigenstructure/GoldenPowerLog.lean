/- GID: D5/S1/Eigenstructure/GoldenPowerLog
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/GoldenPowerLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The logarithmic scale of every natural golden power is integral. -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Eigenstructure.GoldenPowerLog

/-- The natural powers of the golden ratio lie on integral logarithmic levels. -/
theorem golden_power_logb_nat (n : ℕ) :
    Real.logb Real.goldenRatio (Real.goldenRatio ^ n) = (n : ℝ) := by
  rw [Real.logb_pow, Real.logb_self_eq_one Real.one_lt_goldenRatio]
  norm_num

end D5.S1.Eigenstructure.GoldenPowerLog
