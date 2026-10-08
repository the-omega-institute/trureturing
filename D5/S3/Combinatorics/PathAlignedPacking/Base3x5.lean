/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base3x5
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base3x5
   mirror-E: none(waiver:direct-formalization-of-path-aligned-packing)
   anchors: []
   utility: none
   digest: An arithmetic certificate for base arcs 3,5 and 5 colours. -/

import D5.S3.Combinatorics.PathAlignedPacking.Schemes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base3x5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs Metric Schemes

private def scheme : Scheme where
  a := 3
  b := 5
  period := 2
  colours := 5
  pumpA := false
  pumpB := true
  colour := ![![1, 2, 1, 4, 1, 2, 1, 3],
      ![1, 2, 1, 5, 1, 2, 1, 3]]

/-- The template extends to all allowed repetitions of its four-vertex prefixes. -/
theorem colouring (ka kb : ℤ) (hka : 0 ≤ ka) (hkb : 0 ≤ kb) (hka0 : ka = 0) :
    HasMetricColor (3 + 4 * ka) (5 + 4 * kb) 5 := by
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
  · intro _; exact hka0
  · simp [scheme]

end D5.S3.Combinatorics.PathAlignedPacking.Base3x5
