/- GID: D5/S1/Dynamics/GoldenFractionalPart
   generality: I
   mirror-B: D5/B/S1/Dynamics/GoldenFractionalPart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Natural golden-rotation indices have canonical fractional representatives. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Dynamics

/-- The representative `{n * phi}` of the natural golden rotation in `[0, 1)`. -/
noncomputable def goldenFractionalPart (n : ℕ) : ℝ :=
  Int.fract ((n : ℝ) * Real.goldenRatio)

end D5.S1.Dynamics
