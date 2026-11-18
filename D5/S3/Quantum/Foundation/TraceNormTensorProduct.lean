/- GID: D5/S3/Quantum/Foundation/TraceNormTensorProduct
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TraceNormTensorProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace-norm multiplicativity for finite rectangular tensor products. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance

/-! Trace-norm multiplicativity for rectangular Kronecker products. -/

set_option autoImplicit false

noncomputable section

/- The declaration namespace preserves the XuImaiGuhneSimultaneousUnboundedness API.
   proof_shape: bind-only; escape_witness: none; consumers: traceNorm_tensor,
   Toolkit.pure_partialTranspose_norm, WChannel.refined_output_norm_bound,
   Amplification.amplify_normC, Amplification.amplify_normA,
   Amplification.amplify_normB, BaseValues.decodedRaw_norms. -/
namespace D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteTraceDistance

variable {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]

theorem traceNorm_kronecker (A : Matrix a b ℂ) (B : Matrix c d ℂ) : traceNorm (A ⊗ₖ B) = traceNorm A * traceNorm B := by
  let P := CFC.sqrt (Aᴴ * A)
  let Q := CFC.sqrt (Bᴴ * B)
  have hP : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hQ : Q.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hs : (P ⊗ₖ Q) * (P ⊗ₖ Q) = (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    dsimp only [P, Q]
    rw [CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg,
      CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self B).nonneg]
  have hroot := CFC.sqrt_unique hs (hP.kronecker hQ).nonneg
  have hPi := (Complex.nonneg_iff.mp hP.trace_nonneg).2
  have hQi := (Complex.nonneg_iff.mp hQ.trace_nonneg).2
  change (CFC.sqrt ((A ⊗ₖ B)ᴴ * (A ⊗ₖ B))).trace.re = P.trace.re * Q.trace.re
  rw [hroot, Matrix.trace_kronecker]
  simp only [Complex.mul_re, hPi.symm, hQi.symm, zero_mul, sub_zero]
end D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit
