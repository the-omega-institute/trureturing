/- GID: D5/S0/Tower/QuadraticFixedPoint
   generality: G
   mirror-B: D5/B/S0/Tower/QuadraticFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero real satisfies x^2 = x + 1 exactly when it satisfies x = 1 + 1/x. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S0.Tower.QuadraticFixedPoint

theorem quadratic_fixed_point_iff (x : ℝ) (hx : x ≠ 0) :
    x ^ 2 = x + 1 ↔ x = 1 + 1 / x := by
  constructor
  · intro h
    field_simp [hx]
    nlinarith
  · intro h
    field_simp [hx] at h
    nlinarith

end D5.S0.Tower.QuadraticFixedPoint
