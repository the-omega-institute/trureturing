/- GID: D5/S3/Quantum/Lieb/WeightedTraceInverseAntitone
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Order-reversing bridge for the weighted trace of matrix inverses. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
import D5.S3.Quantum.Lieb.TraceInverseConvexity
import D5.S3.Weil.ZetaLinear.RankTrace

noncomputable section
namespace D5.S3.Quantum.Lieb.TraceInverseConvexity

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma weighted_trace_re_mono_bridge (C : Matrix d d ℂ) (hC : C.PosSemidef)
    {A B : Matrix d d ℂ} (h : A ≤ B) :
    (Matrix.trace (C * A)).re ≤ (Matrix.trace (C * B)).re := by
  have hpsd : (B - A).PosSemidef := Matrix.le_iff.mp h
  have htr : 0 ≤ (Matrix.trace (C * (B - A))).re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hC hpsd
  rw [Matrix.mul_sub, Matrix.trace_sub] at htr
  exact sub_nonneg.mp htr

/-- A positive witness reverses the trace of the inverse along the positive-definite order.

This is the order companion to `weighted_trace_inverse_convexOn`; it is the
finite-dimensional monotonicity bridge used by divergence constructions. -/
theorem weighted_trace_inverse_antitone (C : Matrix d d ℂ) (hC : C.PosSemidef) :
    AntitoneOn (fun A : Matrix d d ℂ => (Matrix.trace (C * A⁻¹)).re)
      {A : Matrix d d ℂ | A.PosDef} := by
  intro A hA B hB hAB
  have hmatrix : B⁻¹ ≤ A⁻¹ := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      (CStarAlgebra.antitoneOn_ringInverse hA.isStrictlyPositive
        hB.isStrictlyPositive hAB)
  exact weighted_trace_re_mono_bridge C hC hmatrix

#print axioms weighted_trace_inverse_antitone
end D5.S3.Quantum.Lieb.TraceInverseConvexity
