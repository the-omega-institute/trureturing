/- GID: D5/S1/FixedPoints/ThreeCycleGap
   generality: I
   mirror-B: D5/B/S1/FixedPoints/ThreeCycleGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The three-state successor cycle has distinct least and greatest fixed points. -/

import D5.S1.Dynamics.KnasterTarski

namespace D5.S1.FixedPoints.ThreeCycleGap

open D5.S1.Dynamics.KnasterTarski

/-- The ungrounded three-state cycle separates its least and greatest fixed
points: the inductive solution is empty while the coinductive solution is full. -/
theorem three_cycle_has_fixed_point_gap :
    threeCycleOperator.lfp ≠ threeCycleOperator.gfp := by
  rw [three_cycle_extremal_fixed_points.1, three_cycle_extremal_fixed_points.2]
  intro h
  have hMember : ThreeState.first ∈ (∅ : Set ThreeState) := by
    rw [h]
    trivial
  exact hMember

-- The concrete state domain is inhabited.
example : ThreeState := ThreeState.first

end D5.S1.FixedPoints.ThreeCycleGap
