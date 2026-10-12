/- GID: D5/S3/Quantum/Lieb/TracePerspectiveConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/TracePerspectiveConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint trace perspective convexity from the all-Hilbert power supplier. -/

import D5.S3.Quantum.Lieb.PowerConvexity
import D5.S3.Quantum.Lieb.LiebConcavity

noncomputable section
namespace D5.S3.Quantum.Lieb.TracePerspectiveConvexity
universe u
open LownerHeinzTheorem GeneralizedPerspectiveFunction HilbertSchmidtOperatorSpace
open OperatorGeometricMean LiebAndoTrace
variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

/-- Classical Ando trace perspective convexity; K is arbitrary and its adjoint is retained. -/
theorem trace_perspective_jointly_convex {a : ℝ} (ha : a ∈ Set.Icc 1 2) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) a K) := by
  exact liebTrace_jointlyConvexOn_pdSet ha.1 ha.2 K

#print axioms trace_perspective_jointly_convex
end D5.S3.Quantum.Lieb.TracePerspectiveConvexity
