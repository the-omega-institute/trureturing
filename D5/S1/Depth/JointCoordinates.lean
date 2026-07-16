/- GID: D5/S1/Depth/JointCoordinates
   generality: I
   mirror-B: D5/B/S1/Depth/JointCoordinates
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Joint golden coordinates combine scale, W digits, phase, and finite depth. -/

import D5.S1.Depth.Finite

namespace D5.S1.Depth

open D5.S0.Carrier D5.S0.Conventions
open D5.S1.Digit D5.S1.Phase D5.S1.Scale

/-- The joint coordinate `(A, Z, G)` before finite phase quantization. -/
structure JointCoordinates where
  scale : Option ℤ
  digits : CanonicalRawDigits
  phase : AddCircle (1 : ℝ)

/-- Combine scale of `x` with the digit and phase coordinates of `n`. -/
noncomputable def jointCoordinates (x : GoldenInt) (n : ℕ) : JointCoordinates where
  scale := logScale x
  digits := digitCoordinate n
  phase := phaseCoordinate n

/-- Exact formal echo of the joint coordinate and finite-depth definition. -/
theorem joint_coordinates_spec (x : GoldenInt) (n : ℕ+) (hx : x ≠ 0) (q0 : ℤ) :
    (jointCoordinates x n).scale =
        some ⌊Real.logb Real.goldenRatio |embedding x|⌋ ∧
      (jointCoordinates x n).digits = digitCoordinate n ∧
      (jointCoordinates x n).phase = goldenPhase (n : ℤ) ∧
      phaseResolution q0 n = wValue (resolutionIndex q0 n) ∧
      depth q0 n =
        (scaleCoordinate n, digitLength n,
          finitePhase (phaseResolution q0 n) (phaseResolution_pos q0 n)
            (goldenPhase (n : ℤ))) := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  simpa [jointCoordinates] using logScale_ne_zero hx

end D5.S1.Depth
