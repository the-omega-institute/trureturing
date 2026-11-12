/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Actual all-L1 maximal convex equality on the common interior. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
import D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral
open D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
open D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex

variable {n : Type*} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}

/-- The actual infimum over every s-finite source in the arbitrary universe u,
with positive complex-linear trace-preserving preparation on its entire L1 space. -/
def allL1Value (hf : ConvexOn ℝ (Ioi 0) f) (A B : Matrix n n ℂ) : EReal :=
  sInf (allL1Costs.{u} hf A B)

/-- Exact source atomization identifies the actual all-L1 infimum with the
finite maximal value for the same generator and closed-perspective convention. -/
theorem allL1Value_eq_maximalValue (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) : allL1Value.{u} hf A B = maximalValue hf A B := by
  exact source_class_infimum_eq hf A B

/-- Common-interior commutation suffices for every real convex generator as an
equality of extended actual all-L1 and PSD-overlap hockey values. -/
theorem commute_implies_integrated_eq (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hc : let S := A + B
      let C := MaximalHockeyStickSupport.normalize S A
      let P := interiorProjection C
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P)) :
    allL1Value.{u} hf A B = hockeyValue hf A B := by
  rw [allL1Value_eq_maximalValue]
  exact MaximalHockeyStickConvex.commute_implies_integrated_eq hf A B hA hB hc

/-- For actual full-support curvature and a real finite actual all-L1 infimum,
equality holds exactly when the original common-interior compressions commute.
No optimizer, trace normalization or nonsingularity is assumed. -/
theorem integrated_eq_iff_commute (hf : ConvexOn ℝ (Ioi 0) f)
    [(curvature hf).IsOpenPosMeasure]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : allL1Value.{u} hf A B = (c : EReal)) :
    let S := A + B
    let C := MaximalHockeyStickSupport.normalize S A
    let P := interiorProjection C
    (allL1Value.{u} hf A B = hockeyValue hf A B) ↔
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by
  dsimp only
  constructor
  · intro he
    rw [allL1Value_eq_maximalValue] at hc he
    exact (MaximalHockeyStickConvex.integrated_eq_iff_commute hf A B hA hB c hc).1 he
  · exact commute_implies_integrated_eq hf A B hA hB

#print axioms allL1Value_eq_maximalValue
#print axioms commute_implies_integrated_eq
#print axioms integrated_eq_iff_commute

end D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
