/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base10_1
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base10_1
   mirror-E: none(waiver:direct-formalization-of-path-aligned-packing)
   anchors: []
   utility: none
   digest: An arithmetic certificate for base arcs 10,1 and 5 colours. -/

import D5.S3.Combinatorics.PathAlignedPacking.Base10_1.Phase0
import D5.S3.Combinatorics.PathAlignedPacking.Base10_1.Phase1
import D5.S3.Combinatorics.PathAlignedPacking.Base10_1.Phase2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base10_1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs Metric Schemes Data

/-- The template extends to all allowed repetitions of its four-vertex prefixes. -/
theorem colouring (ka kb : ℤ) (hka : 0 ≤ ka) (hkb : 0 ≤ kb) (hkb0 : kb = 0) :
    HasMetricColor (10 + 4 * ka) (1 + 4 * kb) 5 := by
  have formed : WellFormed scheme := by unfold WellFormed; decide +kernel
  have safe : Safe scheme := by
    constructor
    · decide +kernel
    · intro i
      fin_cases i
      · exact Phase0.safe
      · exact Phase1.safe
      · exact Phase2.safe
  apply exists_metric scheme formed safe ka kb
  refine ⟨hka, hkb, ?_, ?_⟩
  · simp [scheme]
  · intro _; exact hkb0

end D5.S3.Combinatorics.PathAlignedPacking.Base10_1
