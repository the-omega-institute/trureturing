/- GID: D5/S3/Constants/Midslope/ThreeValueEvaluation
   generality: G
   mirror-B: D5/B/S3/Constants/Midslope/ThreeValueEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The three elementary midslope-curvature values are exact. -/

import D5.S3.Constants.MidslopeCurvatureValues

namespace D5.S3.Constants.Midslope.ThreeValueEvaluation

open D5.S3.Constants.MidslopeCurvature
open D5.S3.Constants.MidslopeCurvatureValues

/-- The arithmetic, geometric, and harmonic midslope-curvature integrals have their exact values. -/
theorem three_value_evaluation :
    J_one = -Real.log 2 ∧
      J_zero = 1 - 2 * Real.log 2 ∧
        J_neg_one = 0 :=
  ⟨J_one_eq_neg_log_two,
    J_zero_eq_one_sub_two_log_two,
    J_neg_one_eq_zero⟩

#print axioms three_value_evaluation

end D5.S3.Constants.Midslope.ThreeValueEvaluation
