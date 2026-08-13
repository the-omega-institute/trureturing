/- GID: D5/S0/Tower/GoldenFixedPoint
   generality: G
   mirror-B: D5/B/S0/Tower/GoldenFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The real golden ratio satisfies the reciprocal fixed-point equation. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S0.Tower.GoldenFixedPoint

/- Provenance: Thin wrapper around mathlib's reciprocal and conjugate identities. -/

theorem golden_ratio_reciprocal_fixed_point :
    Real.goldenRatio = 1 + 1 / Real.goldenRatio := by
  rw [one_div, Real.inv_goldenRatio, ← sub_eq_add_neg, Real.one_sub_goldenRatio]

end D5.S0.Tower.GoldenFixedPoint
