/- GID: D5/S3/Observer/Approximation/IntertwiningDefectBounds
   generality: G
   mirror-B: D5/B/S3/Observer/Approximation/IntertwiningDefectBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Weighted and uniform norm bounds jointly audit an iterated intertwining defect. -/

import D5.S3.Observer.Approximation.IntertwiningDefectPropagation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Approximation.IntertwiningDefectBounds

open scoped BigOperators

theorem intertwining_defect_propagation_bounds
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (A : Y →L[𝕜] Y) (C : X →L[𝕜] Y) (T : X →L[𝕜] X)
    (L : ℝ) (n : Nat) :
    (‖C.comp (T ^ n) - (A ^ n).comp C‖ ≤
      ∑ j ∈ Finset.range n,
        ‖A‖ ^ (n - 1 - j) *
          ‖D5.S3.Observer.Approximation.IntertwiningDefectPropagation.intertwiningDefect
            A C T‖ * ‖T‖ ^ j) ∧
    (‖A‖ ≤ L → ‖T‖ ≤ L →
      ‖C.comp (T ^ n) - (A ^ n).comp C‖ ≤
        (n : ℝ) * L ^ (n - 1) *
          ‖D5.S3.Observer.Approximation.IntertwiningDefectPropagation.intertwiningDefect
            A C T‖) := by
  constructor
  · exact
      D5.S3.Observer.Approximation.IntertwiningDefectPropagation.norm_intertwining_defect_le
        A C T n
  · intro hA hT
    exact
      D5.S3.Observer.Approximation.IntertwiningDefectPropagation.uniform_norm_intertwining_defect_le
        A C T L n hA hT
#print axioms intertwining_defect_propagation_bounds

end D5.S3.Observer.Approximation.IntertwiningDefectBounds
