/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base8_8
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base8_8
   mirror-E: none(waiver:direct-formalization-of-path-aligned-packing)
   anchors: []
   utility: none
   digest: An arithmetic certificate for base arcs 8,8 and 5 colours. -/

import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase0.Offset0
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase0.Offset1
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase0.Offset2
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase0.Offset3
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase1.Offset0
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase1.Offset1
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase1.Offset2
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase1.Offset3
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase2.Offset1
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase2.Offset2
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase2.Offset3
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase3.Offset0
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase3.Offset1
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase3.Offset2
import D5.S3.Combinatorics.PathAlignedPacking.Base8_8.Phase3.Offset3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base8_8

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs Metric Schemes Data

/-- The template extends to all allowed repetitions of its four-vertex prefixes. -/
theorem colouring (ka kb : ℤ) (hka : 0 ≤ ka) (hkb : 0 ≤ kb) :
    HasMetricColor (8 + 4 * ka) (8 + 4 * kb) 5 := by
  have formed : WellFormed scheme := by unfold WellFormed; decide +kernel
  have safe : Safe scheme := by
    constructor
    · decide +kernel
    · intro i d
      fin_cases i <;> fin_cases d
      · exact Phase0.Offset0.safe
      · exact Phase0.Offset1.safe
      · exact Phase0.Offset2.safe
      · exact Phase0.Offset3.safe
      · exact Phase1.Offset0.safe
      · exact Phase1.Offset1.safe
      · exact Phase1.Offset2.safe
      · exact Phase1.Offset3.safe
      · exact Phase1.Offset0.safe
      · exact Phase2.Offset1.safe
      · exact Phase2.Offset2.safe
      · exact Phase2.Offset3.safe
      · exact Phase3.Offset0.safe
      · exact Phase3.Offset1.safe
      · exact Phase3.Offset2.safe
      · exact Phase3.Offset3.safe
  apply exists_metric scheme formed safe ka kb
  refine ⟨hka, hkb, ?_, ?_⟩
  · simp [scheme]
  · simp [scheme]

end D5.S3.Combinatorics.PathAlignedPacking.Base8_8
