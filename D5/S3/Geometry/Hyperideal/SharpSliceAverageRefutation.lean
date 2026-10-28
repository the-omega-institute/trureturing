/- GID: D5/S3/Geometry/Hyperideal/SharpSliceAverageRefutation
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SharpSliceAverageRefutation
   mirror-E: none(waiver:sharp-slice-average-certificate)
   anchors: []
   utility: none
   digest: Exact rational determinant certificates for the sharp-slice averaging reversal. -/

import D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.SharpSliceAverageRefutation

open D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder

def averaged_truth_implies_original_truth : Prop :=
    (gram (49 / 10 : Real) (49 / 10) 2 2 0 0).det < 0 →
      (gram (49 / 10 : Real) (49 / 10) 2 2 (4 / 5) 0).det < 0

theorem sharp_slice_average_refutation :
    ¬ averaged_truth_implies_original_truth := by
  intro h
  have havg : (gram (49 / 10 : Real) (49 / 10) 2 2 0 0).det < 0 := by
    rw [determinant_remainder_identity]
    norm_num [L, M, Xi]
  have horig := h havg
  rw [determinant_remainder_identity] at horig
  norm_num [L, M, Xi] at horig

#print axioms sharp_slice_average_refutation

end D5.S3.Geometry.Hyperideal.SharpSliceAverageRefutation
