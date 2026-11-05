/- GID: D5/S3/Quantum/Lieb/TraceInverseConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/TraceInverseConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-dimensional trace bridge for operator-convex matrix inversion. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
import D5.S3.Weil.ZetaLinear.RankTrace

/-! Finite-dimensional trace bridge for operator-convex matrix inversion. -/

noncomputable section
namespace D5.S3.Quantum.Lieb.TraceInverseConvexity

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma trace_re_mono {A B : Matrix d d ℂ} (h : A ≤ B) :
    (Matrix.trace A).re ≤ (Matrix.trace B).re := by
  have hpsd : (B - A).PosSemidef := Matrix.le_iff.mp h
  have htr : 0 ≤ (Matrix.trace (B - A)).re :=
    (Complex.nonneg_iff.mp hpsd.trace_nonneg).1
  rw [Matrix.trace_sub, Complex.sub_re] at htr
  exact sub_nonneg.mp htr

private lemma weighted_trace_re_mono (C : Matrix d d ℂ) (hC : C.PosSemidef)
    {A B : Matrix d d ℂ} (h : A ≤ B) :
    (Matrix.trace (C * A)).re ≤ (Matrix.trace (C * B)).re := by
  have hpsd : (B - A).PosSemidef := Matrix.le_iff.mp h
  have htr : 0 ≤ (Matrix.trace (C * (B - A))).re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hC hpsd
  rw [Matrix.mul_sub, Matrix.trace_sub] at htr
  exact sub_nonneg.mp htr

/-- A fixed positive witness preserves inverse convexity after taking a trace. -/
theorem weighted_trace_inverse_convexOn (C : Matrix d d ℂ) (hC : C.PosSemidef) :
    ConvexOn ℝ {A : Matrix d d ℂ | A.PosDef}
      (fun A => (Matrix.trace (C * A⁻¹)).re) := by
  let hconv := CStarAlgebra.convexOn_ringInverse (A := Matrix d d ℂ)
  refine ⟨?_, ?_⟩
  · intro A hA B hB a b ha hb hab
    exact (hconv.1 hA.isStrictlyPositive hB.isStrictlyPositive ha hb hab).posDef
  · intro A hA B hB a b ha hb hab
    have hmatrix := hconv.2 hA.isStrictlyPositive hB.isStrictlyPositive ha hb hab
    have hmatrix' :
        (a • A + b • B)⁻¹ ≤ a • A⁻¹ + b • B⁻¹ := by
      simpa only [Matrix.nonsing_inv_eq_ringInverse] using hmatrix
    have htrace := weighted_trace_re_mono C hC hmatrix'
    simpa only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul] using htrace

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
  exact weighted_trace_re_mono C hC hmatrix

/-- The real trace of the inverse is convex on the positive-definite cone.

This is the finite-matrix scalar bridge from Mathlib's operator convexity of
`Ring.inverse` to the trace function used by quantum divergences. -/
theorem trace_inverse_convexOn :
    ConvexOn ℝ {A : Matrix d d ℂ | A.PosDef}
      (fun A => (Matrix.trace A⁻¹).re) := by
  simpa only [Matrix.one_mul] using
    (weighted_trace_inverse_convexOn (d := d) (1 : Matrix d d ℂ)
      Matrix.PosSemidef.one)

#print axioms trace_inverse_convexOn
#print axioms weighted_trace_inverse_convexOn
end D5.S3.Quantum.Lieb.TraceInverseConvexity
