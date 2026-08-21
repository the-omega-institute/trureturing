/- GID: D5/S3/Quantum/Divergence/RelativeEntropyDefectComposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/RelativeEntropyDefectComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relative-entropy loss telescopes exactly along two composable state channels. -/

import D5.S3.Observer.DefectComposition.StrictDefectComposition

namespace D5.S3.Quantum.Divergence.RelativeEntropyDefectComposition

open D5.S3.Observer.DefectComposition.StrictDefectComposition

/-- The relative-entropy defect of two successive state channels is the sum of their defects. -/
theorem relative_entropy_defect_composition
    {StateA StateB StateC : Type*}
    (relativeEntropyA : StateA → StateA → ℝ)
    (relativeEntropyB : StateB → StateB → ℝ)
    (relativeEntropyC : StateC → StateC → ℝ)
    (firstChannel : StateA → StateB)
    (secondChannel : StateB → StateC)
    (rho sigma : StateA) :
    strictDefect relativeEntropyA relativeEntropyC (secondChannel ∘ firstChannel) rho sigma =
      strictDefect relativeEntropyA relativeEntropyB firstChannel rho sigma +
        strictDefect relativeEntropyB relativeEntropyC secondChannel
          (firstChannel rho) (firstChannel sigma) :=
  strict_defect_composition relativeEntropyA relativeEntropyB relativeEntropyC
    firstChannel secondChannel rho sigma

#print axioms relative_entropy_defect_composition

end D5.S3.Quantum.Divergence.RelativeEntropyDefectComposition
