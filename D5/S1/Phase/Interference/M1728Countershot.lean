/- GID: D5/S1/Phase/Interference/M1728Countershot
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/M1728Countershot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A concrete alternating walk evaluates to -48, divisible by 24 and 48. -/

import D5.S1.Phase.WalkFormula

namespace D5.S1.Phase.Interference.M1728Countershot

open D5.S1.Phase.WalkFormula

/- The concrete address is retained in the statement so the certificate cannot
   be discharged by an uninhabited or unconstrained predicate. -/
theorem m1728_countershot :
    alternatingWalk [1, 1, 23, 1, 1, 71] = -48 ∧
      (-48 : Int) % 24 = 0 ∧
      (-48 : Int) % 48 = 0 := by
  constructor
  · norm_num [alternatingWalk]
  constructor <;> decide

theorem m1728_countershot_witness :
    alternatingWalk [1, 1, 23, 1, 1, 71] = -48 ∧
      (-48 : Int) ≠ 0 := by
  constructor
  · norm_num [alternatingWalk]
  · decide

end D5.S1.Phase.Interference.M1728Countershot
