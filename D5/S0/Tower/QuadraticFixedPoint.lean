/- GID: D5/S0/Tower/QuadraticFixedPoint
   generality: G
   mirror-B: D5/B/S0/Tower/QuadraticFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero real satisfies x^2 = x + 1 exactly when it satisfies x = 1 + 1/x. -/

import Mathlib.Tactic

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

example : Nonempty ℝ := inferInstance

example : (1 : ℝ) ≠ 0 := one_ne_zero

example : ¬ ((1 : ℝ) ^ 2 = 1 + 1) := by norm_num

#print axioms quadratic_fixed_point_iff

end D5.S0.Tower.QuadraticFixedPoint
