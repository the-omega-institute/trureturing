/- GID: D5/S3/QuantumStates/GNSExpectation
   generality: G
   mirror-B: D5/B/S3/QuantumStates/GNSExpectation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Lift the GNS expectation identity to arbitrary C-star algebras. -/

import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

namespace D5.S3.QuantumStates.GNSExpectation

open scoped ComplexOrder

/-- A positive linear functional evaluates `star x * x` as the squared norm of the
corresponding pre-GNS vector. -/
theorem expectation_eq_preGNS_norm_sq {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (omega : A →ₚ[ℂ] ℂ) (x : A) :
    omega (star x * x) = ((‖omega.toPreGNS x‖ ^ 2 : ℝ) : ℂ) := by
  simpa using (omega.preGNS_norm_sq (omega.toPreGNS x)).symm

#print axioms expectation_eq_preGNS_norm_sq

end D5.S3.QuantumStates.GNSExpectation
