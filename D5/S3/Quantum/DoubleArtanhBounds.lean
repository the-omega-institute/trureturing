/- GID: D5/S3/Quantum/DoubleArtanhBounds
   generality: G
   mirror-B: D5/B/S3/Quantum/DoubleArtanhBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound Real.artanh above and below on the open unit interval. -/

import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace D5.S3.Quantum.DoubleArtanhBounds

/-- The real inverse hyperbolic tangent lies between two rational bounds on `(0, 1)`. -/
theorem double_artanh_bounds
    (u : ℝ) (hu : 0 < u) (hu_one : u < 1) :
    Real.artanh u ≤ u / (1 - u ^ 2) ∧
      u / (1 + u ^ 2) ≤ Real.artanh u := by
  rw [Real.artanh_eq_half_log (by constructor <;> linarith)]
  constructor
  · simpa using Real.log_div_le_sum_range_add hu.le hu_one 0
  · refine (div_le_self hu.le ?_).trans ?_
    · nlinarith [sq_nonneg u]
    · simpa using Real.sum_range_le_log_div hu.le hu_one 1

end D5.S3.Quantum.DoubleArtanhBounds
