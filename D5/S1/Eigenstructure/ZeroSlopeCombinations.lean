/- GID: D5/S1/Eigenstructure/ZeroSlopeCombinations
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/ZeroSlopeCombinations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonzero drift slopes have a codimension-one zero-slope combination space. -/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace D5.S1.Eigenstructure.ZeroSlopeCombinations

/-- The zero-slope linear combinations for a nonzero drift functional form a
codimension-one subspace of the coefficients on a finite cycle. -/
theorem zero_slope_combinations_finrank_add_one {cycleLength : ℕ}
    (slope : Module.Dual ℝ (Fin cycleLength → ℝ)) (hslope : slope ≠ 0) :
    Module.finrank ℝ (LinearMap.ker slope) + 1 = cycleLength := by
  simpa only [Module.finrank_fin_fun] using
    Module.Dual.finrank_ker_add_one_of_ne_zero hslope

end D5.S1.Eigenstructure.ZeroSlopeCombinations
