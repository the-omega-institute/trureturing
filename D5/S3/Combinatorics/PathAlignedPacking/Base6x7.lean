/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base6x7
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base6x7
   mirror-E: none(waiver:direct-formalization-of-path-aligned-packing)
   anchors: []
   utility: none
   digest: An arithmetic certificate for base arcs 6,7 and 5 colours. -/

import D5.S3.Combinatorics.PathAlignedPacking.Base6x7.Phase0.Near
import D5.S3.Combinatorics.PathAlignedPacking.Base6x7.Phase0.Far
import D5.S3.Combinatorics.PathAlignedPacking.Base6x7.Phase1.Near
import D5.S3.Combinatorics.PathAlignedPacking.Base6x7.Phase1.Far
import D5.S3.Combinatorics.PathAlignedPacking.Base6x7.Phase2.Near
import D5.S3.Combinatorics.PathAlignedPacking.Base6x7.Phase2.Far
import D5.S3.Combinatorics.PathAlignedPacking.Base6x7.Phase3.Near
import D5.S3.Combinatorics.PathAlignedPacking.Base6x7.Phase3.Far

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base6x7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs Metric Schemes Data

/-- The template extends to all allowed repetitions of its four-vertex prefixes. -/
theorem colouring (ka kb : ℤ) (hka : 0 ≤ ka) (hkb : 0 ≤ kb) :
    HasMetricColor (6 + 4 * ka) (7 + 4 * kb) 5 := by
  have formed : WellFormed scheme := by unfold WellFormed; decide +kernel
  have safe : Safe scheme := by
    constructor
    · decide +kernel
    · intro i d
      fin_cases i <;> fin_cases d
      · exact Phase0.Near.safe 0
      · exact Phase0.Near.safe 1
      · exact Phase0.Far.safe 0
      · exact Phase0.Far.safe 1
      · exact Phase1.Near.safe 0
      · exact Phase1.Near.safe 1
      · exact Phase1.Far.safe 0
      · exact Phase1.Far.safe 1
      · exact Phase2.Near.safe 0
      · exact Phase2.Near.safe 1
      · exact Phase2.Far.safe 0
      · exact Phase2.Far.safe 1
      · exact Phase3.Near.safe 0
      · exact Phase3.Near.safe 1
      · exact Phase3.Far.safe 0
      · exact Phase3.Far.safe 1
  apply exists_metric scheme formed safe ka kb
  refine ⟨hka, hkb, ?_, ?_⟩
  · simp [scheme]
  · simp [scheme]

end D5.S3.Combinatorics.PathAlignedPacking.Base6x7
