/- GID: D5/S1/Depth/JointDepth
   generality: I
   mirror-B: D5/B/S1/Depth/JointDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admissible finite depth uses the same point for scale and W-indexed resolution. -/

import D5.S1.Depth.JointCoordinates

namespace D5.S1.Depth

open D5.S0.Carrier D5.S0.Conventions
open D5.S1.Digit D5.S1.Phase
open D5.S1.Scale

/-- The logarithmic A-coordinate of the same point used by the joint coordinate. -/
noncomputable def jointScaleCoordinate (x : GoldenInt) : ℤ :=
  ⌊Real.logb Real.goldenRatio |embedding x|⌋

/-- The W-resolution index `A(x) + q0` must be a natural index. -/
def JointResolutionAdmissible (x : GoldenInt) (q0 : ℤ) : Prop :=
  0 ≤ jointScaleCoordinate x + q0

/-- The natural W index underlying `Q(x)`. -/
noncomputable def jointResolutionIndex (x : GoldenInt) (q0 : ℤ) : ℕ :=
  (jointScaleCoordinate x + q0).toNat

/-- Admissibility makes the natural resolution index equal to `A(x) + q0`. -/
theorem joint_resolution_index_spec {x : GoldenInt} {q0 : ℤ}
    (hQ : JointResolutionAdmissible x q0) :
    (jointResolutionIndex x q0 : ℤ) = jointScaleCoordinate x + q0 := by
  exact Int.toNat_of_nonneg hQ

/-- The finite phase resolution `Q(x) = W_(A(x)+q0)`. -/
noncomputable def jointPhaseResolution (x : GoldenInt) (q0 : ℤ) : ℕ :=
  wValue (jointResolutionIndex x q0)

theorem jointPhaseResolution_pos (x : GoldenInt) (q0 : ℤ) :
    0 < jointPhaseResolution x q0 := by
  rw [jointPhaseResolution, wValue]
  exact Nat.fib_pos.2 (by omega)

/-- The dependent finite-depth codomain at a point and resolution offset. -/
abbrev JointDepthValue (x : GoldenInt) (q0 : ℤ) :=
  ℤ × ℕ × Fin (jointPhaseResolution x q0)

/-- The finite tuple `(A(x), |Z(n)|, H_(Q(x))(G(n)))`. -/
noncomputable def jointDepth (x : GoldenInt) (n : ℕ) (q0 : ℤ) :
    JointDepthValue x q0 :=
  (jointScaleCoordinate x, digitLength n,
    finitePhase (jointPhaseResolution x q0) (jointPhaseResolution_pos x q0)
      (phaseCoordinate n))

/-- Exact admissible echo of the joint coordinate and `Q(x)` finite depth. -/
theorem joint_depth_spec (x : GoldenInt) (n : ℕ) (hx : x ≠ 0)
    (q0 : ℤ) (hQ : JointResolutionAdmissible x q0) :
    (jointCoordinates x n).scale = some (jointScaleCoordinate x) ∧
      (jointCoordinates x n).digits.1 = toRaw (Z n) ∧
      (jointCoordinates x n).phase = goldenPhase (n : ℤ) ∧
      (jointResolutionIndex x q0 : ℤ) = jointScaleCoordinate x + q0 ∧
      jointPhaseResolution x q0 = wValue (jointResolutionIndex x q0) ∧
      jointDepth x n q0 =
        (jointScaleCoordinate x, digitLength n,
          finitePhase (jointPhaseResolution x q0)
            (jointPhaseResolution_pos x q0) (goldenPhase (n : ℤ))) := by
  refine ⟨?_, rfl, rfl, joint_resolution_index_spec hQ, rfl, rfl⟩
  simpa [jointCoordinates, jointScaleCoordinate] using logScale_ne_zero hx

end D5.S1.Depth
