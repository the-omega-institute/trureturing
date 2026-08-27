/- GID: D5/S1/FixedPoints/Algebraic/GoldenFixedPoint
   generality: I
   mirror-B: D5/B/S1/FixedPoints/Algebraic/GoldenFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The positive real fixed point of x |-> 1 + 1/x is uniquely the golden ratio. -/

import D5.S0.Carrier.GoldenRatio
import D5.S0.Tower.GoldenFixedPoint
import D5.S0.Tower.QuadraticFixedPoint

/- Library-search audit trail (2026-08-27):
   * Exact repository hits `golden_ratio_reciprocal_fixed_point` and
     `quadratic_fixed_point_iff` supply existence and the reciprocal-to-
     quadratic conversion; both are imported and applied below.
   * Exact repository hit `golden_ratio_spec` and pinned-Mathlib facts
     `Real.goldenRatio_sq` and `Real.goldenRatio_pos` supply the radical,
     quadratic, and positive-root data.
   * Repository, pinned-Mathlib, and Loogle searches found no declaration
     giving uniqueness of this fixed point on the positive reals.
   * LeanSearch returned only its client page; Reservoir's attempted code
     query returned HTTP 404, and anonymous GitHub code search required
     authentication. -/

namespace D5.S1.FixedPoints.Algebraic.GoldenFixedPoint

open D5.S0.Carrier
open D5.S0.Tower.GoldenFixedPoint
open D5.S0.Tower.QuadraticFixedPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The reciprocal residual map from the source definition. -/
noncomputable def goldenReciprocalMap (x : Real) : Real :=
  1 + 1 / x

/-- On the positive reals, the reciprocal residual map has exactly the
displayed radical golden ratio as its fixed point. -/
theorem golden_fixed_point_unique (x : Real) (hx : 0 < x) :
    goldenReciprocalMap x = x ↔ x = (1 + Real.sqrt 5) / 2 := by
  rw [← golden_ratio_spec.1]
  constructor
  · intro hfixed
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hquad : x ^ 2 = x + 1 := by
      apply (quadratic_fixed_point_iff x hx0).2
      exact hfixed.symm
    have hfactor :
        (x - Real.goldenRatio) * (x + Real.goldenRatio - 1) = 0 := by
      nlinarith [hquad, golden_ratio_spec.2.1]
    rcases mul_eq_zero.mp hfactor with hsame | himpossible
    · exact sub_eq_zero.mp hsame
    · exfalso
      have hpositive : 0 < x + Real.goldenRatio - 1 := by
        nlinarith [Real.one_lt_goldenRatio]
      exact (ne_of_gt hpositive) himpossible
  · intro hgolden
    subst x
    change 1 + 1 / Real.goldenRatio = Real.goldenRatio
    exact golden_ratio_reciprocal_fixed_point.symm

/-- Reverse probe: the public characterization recovers the nontrivial
quadratic identity of every positive fixed point. -/
example {x : Real} (hx : 0 < x) (hfixed : goldenReciprocalMap x = x) :
    x ^ 2 = x + 1 := by
  have hgolden := (golden_fixed_point_unique x hx).1 hfixed
  rw [hgolden, ← golden_ratio_spec.1]
  exact golden_ratio_spec.2.1

/-- Trivialization probe: one is not a fixed point of the source map. -/
example : goldenReciprocalMap 1 ≠ 1 := by
  norm_num [goldenReciprocalMap]

#print axioms golden_fixed_point_unique

end D5.S1.FixedPoints.Algebraic.GoldenFixedPoint
