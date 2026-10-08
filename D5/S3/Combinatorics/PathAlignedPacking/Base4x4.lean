/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base4x4
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base4x4
   mirror-E: none(waiver:direct-formalization-of-path-aligned-packing)
   anchors: []
   utility: none
   digest: An arithmetic certificate for base arcs 4,4 and 5 colours. -/

import D5.S3.Combinatorics.PathAlignedPacking.Schemes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base4x4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs Metric Schemes

private def scheme : Scheme where
  a := 4
  b := 4
  period := 4
  colours := 5
  pumpA := false
  pumpB := false
  colour := ![![1, 2, 1, 3, 1, 2, 1, 3],
      ![4, 1, 2, 1, 3, 1, 2, 1],
      ![1, 2, 1, 3, 1, 2, 1, 4],
      ![5, 1, 2, 1, 4, 1, 2, 1]]

/-- The template extends to all allowed repetitions of its four-vertex prefixes. -/
theorem colouring (ka kb : ℤ) (hka : 0 ≤ ka) (hkb : 0 ≤ kb) (hka0 : ka = 0) (hkb0 : kb = 0) :
    HasMetricColor (4 + 4 * ka) (4 + 4 * kb) 5 := by
  have formed : WellFormed scheme := by unfold WellFormed; decide +kernel
  have safe : Safe scheme := by
    constructor
    · decide +kernel
    · intro i d j h ka kb r q hk hr hl hq hql hne heq
      rcases hk with ⟨hka, hkb, hka0, hkb0⟩
      have eka : ka = 0 := hka0 rfl
      have ekb : kb = 0 := hkb0 rfl
      subst ka
      subst kb
      have er : r = 0 := by simp [runLimit, scheme] at hl; omega
      have eq : q = 0 := by simp [runLimit, scheme] at hql; omega
      subst r
      subst q
      clear hr hl hq hql hka hkb hka0 hkb0
      revert heq hne i d j h
      decide +kernel
  apply exists_metric scheme formed safe ka kb
  refine ⟨hka, hkb, ?_, ?_⟩
  · intro _; exact hka0
  · intro _; exact hkb0

end D5.S3.Combinatorics.PathAlignedPacking.Base4x4
