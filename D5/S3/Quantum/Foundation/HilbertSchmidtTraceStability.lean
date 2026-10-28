/- GID: D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/HilbertSchmidtTraceStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hilbert-Schmidt square-root errors bound trace errors under a positive Gram majorant. -/

/-
Auxiliary WIP source for the actual Petz stability proof, not standalone content admission.
All declarations here are bind-only norm/trace closure; the private helpers are consumed
by traceNorm_sub_le_four_hs_sqrt. The public helper is reserved for the actual Petz
consumer and is not independently frozen or claimed as new escape content.
-/

import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM

/-! Hilbert-Schmidt errors control trace errors under a positive Gram majorant. -/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (entryNormSq)

namespace D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem entryNormSq_eq_hs_sq (A : Matrix d d ℂ) :
    entryNormSq A = ‖A‖ ^ 2 := by
  change (∑ i, ∑ j, ‖A i j‖ ^ 2) =
    ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))‖ ^ 2
  simp only [PiLp.norm_sq_eq_of_L2]

private theorem trace_norm_product (A B : Matrix d d ℂ) :
    traceNorm (A * B) ≤ ‖A‖ * ‖B‖ := by
  simpa only [entryNormSq_eq_hs_sq, Real.sqrt_sq_eq_abs, abs_norm] using
    D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq A B

private theorem trace_gram (A : Matrix d d ℂ) :
    (A * Aᴴ).trace.re = ‖A‖ ^ 2 := by
  calc
    (A * Aᴴ).trace.re = (Aᴴ * A).trace.re :=
      congrArg Complex.re (Matrix.trace_mul_comm A Aᴴ)
    _ = ‖A‖ ^ 2 := by
      simpa only [Complex.ofReal_re] using
        (congrArg Complex.re
          (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace A)).symm

private theorem trace_norm_gram_stability (C S N : Matrix d d ℂ)
    (hS : ‖S‖ = 1) (hN : N.trace.re = 1) (hCN : C * Cᴴ ≤ N) :
    traceNorm (N - S * Sᴴ) ≤ 4 * ‖C - S‖ := by
  have hD : (N - C * Cᴴ).PosSemidef := (sub_nonneg.mpr hCN).posSemidef
  have hDnorm : traceNorm (N - C * Cᴴ) = 1 - ‖C‖ ^ 2 := by
    simpa only [RCLike.ofReal_re, RCLike.re_eq_complex_re,
      Matrix.trace_sub, Complex.sub_re, hN, trace_gram] using
      congrArg RCLike.re (traceNorm_of_posSemidef hD)
  have hcSq : ‖C‖ ^ 2 ≤ 1 := by
    have h := traceNorm_nonneg (N - C * Cᴴ)
    rw [hDnorm] at h
    linarith
  have hc : ‖C‖ ≤ 1 := by nlinarith [norm_nonneg C]
  have hreverse : 1 - ‖C‖ ≤ ‖C - S‖ := by
    calc
      1 - ‖C‖ = ‖S‖ - ‖C‖ := by rw [hS]
      _ ≤ ‖S - C‖ := norm_sub_norm_le S C
      _ = ‖C - S‖ := norm_sub_rev S C
  have hdeficit : traceNorm (N - C * Cᴴ) ≤ 2 * ‖C - S‖ := by
    rw [hDnorm]
    calc
      1 - ‖C‖ ^ 2 = (1 - ‖C‖) * (1 + ‖C‖) := by ring
      _ ≤ ‖C - S‖ * (1 + ‖C‖) :=
        mul_le_mul_of_nonneg_right hreverse (by positivity)
      _ ≤ ‖C - S‖ * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ = 2 * ‖C - S‖ := by ring
  have hproduct : traceNorm (C * Cᴴ - S * Sᴴ) ≤ 2 * ‖C - S‖ := by
    calc
      traceNorm (C * Cᴴ - S * Sᴴ) =
          traceNorm ((C - S) * Cᴴ + S * (Cᴴ - Sᴴ)) := by
        congr 1
        noncomm_ring
      _ ≤ traceNorm ((C - S) * Cᴴ) + traceNorm (S * (Cᴴ - Sᴴ)) :=
        traceNorm_add_le _ _
      _ ≤ ‖C - S‖ * ‖Cᴴ‖ + ‖S‖ * ‖Cᴴ - Sᴴ‖ :=
        add_le_add (trace_norm_product _ _) (trace_norm_product _ _)
      _ = (‖C‖ + 1) * ‖C - S‖ := by
        rw [← Matrix.conjTranspose_sub C S]
        simp only [Matrix.frobenius_norm_conjTranspose, hS]
        ring
      _ ≤ 2 * ‖C - S‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  calc
    traceNorm (N - S * Sᴴ) =
        traceNorm ((N - C * Cᴴ) + (C * Cᴴ - S * Sᴴ)) := by
      congr 1
      abel
    _ ≤ traceNorm (N - C * Cᴴ) + traceNorm (C * Cᴴ - S * Sᴴ) :=
      traceNorm_add_le _ _
    _ ≤ 2 * ‖C - S‖ + 2 * ‖C - S‖ := add_le_add hdeficit hproduct
    _ = 4 * ‖C - S‖ := by ring

/-- The exact dimension-free HS-to-trace bridge. -/
theorem traceNorm_sub_le_four_hs_sqrt (C R N : Matrix d d ℂ)
    (hR : R.PosSemidef) (htrR : R.trace = 1) (htrN : N.trace = 1)
    (hCN : C * Cᴴ ≤ N) :
    traceNorm (N - R) ≤ 4 * ‖C - CFC.sqrt R‖ := by
  let S := CFC.sqrt R
  have hstar : Sᴴ = S := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
  have hprod : S * Sᴴ = R := by
    rw [hstar]
    exact CFC.sqrt_mul_sqrt_self R hR.nonneg
  have htraceR : R.trace.re = 1 := by rw [htrR]; rfl
  have htraceN : N.trace.re = 1 := by rw [htrN]; rfl
  have hnormSq : ‖S‖ ^ 2 = 1 := by
    rw [← trace_gram S, hprod, htraceR]
  have hnorm : ‖S‖ = 1 := by nlinarith [norm_nonneg S]
  simpa only [hprod] using trace_norm_gram_stability C S N hnorm htraceN hCN

end D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
