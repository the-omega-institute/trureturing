/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base5x2
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base5x2
   mirror-E: none(waiver:direct-formalization-of-path-aligned-packing)
   anchors: []
   utility: none
   digest: An arithmetic certificate for base arcs 5,2 and 5 colours. -/

import D5.S3.Combinatorics.PathAlignedPacking.Schemes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base5x2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs Metric Schemes

private def scheme : Scheme where
  a := 5
  b := 2
  period := 2
  colours := 5
  pumpA := true
  pumpB := false
  colour := ![![4, 1, 2, 1, 3, 1, 2],
      ![5, 1, 2, 1, 3, 1, 2]]

/-- The template extends to all allowed repetitions of its four-vertex prefixes. -/
theorem colouring (ka kb : ℤ) (hka : 0 ≤ ka) (hkb : 0 ≤ kb) (hkb0 : kb = 0) :
    HasMetricColor (5 + 4 * ka) (2 + 4 * kb) 5 := by
  have formed : WellFormed scheme := by unfold WellFormed; decide +kernel
  have safe : Safe scheme := by
    constructor
    · decide +kernel
    · intro i d j h ka kb r q hk hr hl hq hql hne heq
      rcases hk with ⟨hka, hkb, hka0, hkb0⟩
      fin_cases i <;> fin_cases d <;> fin_cases j <;> fin_cases h <;>
        simp [scheme] at heq <;>
        simp [scheme, runLimit, position, arcA, arcB, chainSep, cycleSep] at * <;>
        omega
  apply exists_metric scheme formed safe ka kb
  refine ⟨hka, hkb, ?_, ?_⟩
  · simp [scheme]
  · intro _; exact hkb0

end D5.S3.Combinatorics.PathAlignedPacking.Base5x2
