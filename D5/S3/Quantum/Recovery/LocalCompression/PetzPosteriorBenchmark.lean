/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzPosteriorBenchmark
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzPosteriorBenchmark
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace-norm drift bound for a commuting-reference Petz benchmark under a flag merger. -/

import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorBin

/-! Trace-norm bounds for merging a normalized bin of commuting-reference Petz posteriors. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorBenchmark

open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability (entryNormSq_eq_hs_sq)
open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM (traceNorm_mul_le_hsSq)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The Hilbert–Schmidt factor of a posterior benchmark with correlation matrix `C`. -/
def posteriorFactor (C : Matrix κ κ ℂ) (v : κ → ℝ) : Matrix κ κ ℂ :=
  diagonal (fun j => (v j : ℂ)) * CFC.sqrt C

private theorem posteriorFactor_gram (C : Matrix κ κ ℂ) (hC : C.PosSemidef) (v : κ → ℝ) :
    posteriorFactor C v * (posteriorFactor C v)ᴴ =
      diagonal (fun j => (v j : ℂ)) * C * diagonal (fun j => (v j : ℂ)) := by
  let d : κ → ℂ := fun j => (v j : ℂ)
  have hd : (diagonal d)ᴴ = diagonal d := by
    rw [Matrix.diagonal_conjTranspose]
    refine congrArg diagonal ?_
    funext j
    change star (v j : ℂ) = (v j : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  have hs : (CFC.sqrt C)ᴴ = CFC.sqrt C := by
    simpa only [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg C).isSelfAdjoint.star_eq
  change (diagonal d * CFC.sqrt C) * (diagonal d * CFC.sqrt C)ᴴ =
    diagonal d * C * diagonal d
  simp only [Matrix.conjTranspose_mul, hd, hs, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt C) (CFC.sqrt C), CFC.sqrt_mul_sqrt_self C hC.nonneg]

/-- A normalized merger moves the benchmark by at most four times the Euclidean gap
between the coordinatewise root mean square and the mean of its posteriors. -/
theorem traceNorm_posteriorBenchmark_sub_le (C : Matrix κ κ ℂ)
    (hC : C.PosSemidef) (hdiag : ∀ j, C j j = 1)
    (w : ι → ℝ) (y : ι → κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hy : ∀ i, ∑ j, (y i j) ^ 2 = 1) :
    let b : κ → ℝ := fun j => ∑ i, w i * y i j
    let u : κ → ℝ := fun j => Real.sqrt (∑ i, w i * (y i j) ^ 2)
    let F := posteriorFactor C
    traceNorm (F u * (F u)ᴴ - ∑ i, w i • (F (y i) * (F (y i))ᴴ)) ≤
      4 * Real.sqrt (∑ j, (u j - b j) ^ 2) := by
  intro b u F
  let A := F u
  let B := F b
  let M := ∑ i, w i • (F (y i) * (F (y i))ᴴ)
  change traceNorm (A * Aᴴ - M) ≤ 4 * Real.sqrt (∑ j, (u j - b j) ^ 2)
  have htraceGram (X : Matrix κ κ ℂ) : (X * Xᴴ).trace.re = ‖X‖ ^ 2 := by
    rw [Matrix.trace_mul_comm X Xᴴ, ← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace,
      Complex.ofReal_re]
  have hfactorSq (v : κ → ℝ) : ‖F v‖ ^ 2 = ∑ j, (v j) ^ 2 := by
    change ‖posteriorFactor C v‖ ^ 2 = _
    rw [← htraceGram, posteriorFactor_gram C hC]
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hdiag, mul_one, ← Complex.ofReal_mul, Complex.ofReal_re, pow_two]
  have huSq (j : κ) : (u j) ^ 2 = ∑ i, w i * (y i j) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have hA : ‖A‖ = 1 := by
    have hsq : ‖A‖ ^ 2 = 1 := by
      change ‖F u‖ ^ 2 = _
      rw [hfactorSq]
      simp only [huSq]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hy, mul_one, hsum]
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_one] using congrArg Real.sqrt hsq
  have hM : M.trace.re = 1 := by
    simp only [M, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.real_smul,
      Complex.re_ofReal_mul, htraceGram, hfactorSq, hy, mul_one, hsum]
  have hmean : (∑ i, w i • F (y i)) = B := by
    ext j k
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, B, F, posteriorFactor,
      Matrix.diagonal_mul, b, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]
  have hmeanAdjoint : (∑ i, w i • (F (y i))ᴴ) = Bᴴ := by
    rw [← hmean, Matrix.conjTranspose_sum]
    simp only [Matrix.conjTranspose_smul, star_trivial]
  have hvariance :
      (∑ i, w i • ((F (y i) - B) * (F (y i) - B)ᴴ)) = M - B * Bᴴ := by
    have hleft : (∑ i, w i • (F (y i) * Bᴴ)) = B * Bᴴ := by
      simp only [← smul_mul_assoc, ← Matrix.sum_mul, hmean]
    have hright : (∑ i, w i • (B * (F (y i))ᴴ)) = B * Bᴴ := by
      simp only [← mul_smul_comm, ← Matrix.mul_sum, hmeanAdjoint]
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, smul_sub,
      Finset.sum_sub_distrib, hleft, hright, ← Finset.sum_smul, hsum, one_smul, M]
    abel
  have hpsd : (M - B * Bᴴ).PosSemidef := by
    rw [← hvariance]
    exact Matrix.posSemidef_sum _ fun i _ =>
      (Matrix.posSemidef_self_mul_conjTranspose (F (y i) - B)).smul (hw i)
  have hdeficit : traceNorm (M - B * Bᴴ) = 1 - ‖B‖ ^ 2 := by
    have hre : (Complex.ofReal (traceNorm (M - B * Bᴴ))).re = (M - B * Bᴴ).trace.re :=
      congrArg Complex.re (traceNorm_of_posSemidef hpsd)
    simpa only [Complex.ofReal_re, Matrix.trace_sub, Complex.sub_re, hM, htraceGram] using hre
  have hB : ‖B‖ ≤ 1 := by
    have h := traceNorm_nonneg (M - B * Bᴴ)
    rw [hdeficit] at h
    apply (sq_le_sq₀ (norm_nonneg B) zero_le_one).1
    simpa only [one_pow] using sub_nonneg.mp h
  have hvariance_le : traceNorm (M - B * Bᴴ) ≤ 2 * ‖A - B‖ := by
    have hreverse : 1 - ‖B‖ ≤ ‖A - B‖ := by
      simpa only [hA] using norm_sub_norm_le A B
    calc
      traceNorm (M - B * Bᴴ) = (1 - ‖B‖) * (1 + ‖B‖) := by rw [hdeficit]; ring
      _ ≤ ‖A - B‖ * (1 + ‖B‖) :=
        mul_le_mul_of_nonneg_right hreverse (by positivity)
      _ ≤ 2 * ‖A - B‖ := by
        rw [mul_comm (2 : ℝ)]
        exact mul_le_mul_of_nonneg_left (by linarith only [hB]) (norm_nonneg _)
  have hholder (X Y : Matrix κ κ ℂ) : traceNorm (X * Y) ≤ ‖X‖ * ‖Y‖ := by
    simpa only [entryNormSq_eq_hs_sq, Real.sqrt_sq_eq_abs, abs_norm] using
      traceNorm_mul_le_hsSq X Y
  have hgram_le : traceNorm (A * Aᴴ - B * Bᴴ) ≤ 2 * ‖A - B‖ := by
    have hsplit : A * Aᴴ - B * Bᴴ = (A - B) * Aᴴ + B * (Aᴴ - Bᴴ) := by
      noncomm_ring
    rw [hsplit]
    calc
      _ ≤ traceNorm ((A - B) * Aᴴ) + traceNorm (B * (Aᴴ - Bᴴ)) := traceNorm_add_le _ _
      _ ≤ ‖A - B‖ * ‖Aᴴ‖ + ‖B‖ * ‖Aᴴ - Bᴴ‖ := add_le_add (hholder _ _) (hholder _ _)
      _ = (1 + ‖B‖) * ‖A - B‖ := by
        rw [← Matrix.conjTranspose_sub]
        simp only [Matrix.frobenius_norm_conjTranspose, hA]
        ring
      _ ≤ 2 * ‖A - B‖ :=
        mul_le_mul_of_nonneg_right (by linarith only [hB]) (norm_nonneg _)
  have hsub : A - B = F (fun j => u j - b j) := by
    ext j k
    simp only [A, B, F, posteriorFactor, Matrix.sub_apply, Matrix.diagonal_mul,
      Complex.ofReal_sub, sub_mul]
  calc
    traceNorm (A * Aᴴ - M) = traceNorm ((A * Aᴴ - B * Bᴴ) + -(M - B * Bᴴ)) := by
      congr 1
      abel
    _ ≤ traceNorm (A * Aᴴ - B * Bᴴ) + traceNorm (-(M - B * Bᴴ)) := traceNorm_add_le _ _
    _ ≤ 4 * ‖A - B‖ := by
      rw [traceNorm_neg]
      linarith only [hgram_le, hvariance_le]
    _ = 4 * Real.sqrt (∑ j, (u j - b j) ^ 2) := by
      rw [hsub, ← hfactorSq (fun j => u j - b j), Real.sqrt_sq_eq_abs, abs_norm]

/-- For posteriors in a common square bin in each coordinate, this bounds the
trace-norm drift of the actual Hermitian benchmark blocks. -/
theorem traceNorm_posteriorBenchmark_square_bin_le (C : Matrix κ κ ℂ)
    (hC : C.PosSemidef) (hdiag : ∀ j, C j j = 1)
    (w : ι → ℝ) (y : ι → κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hy : ∀ i, ∑ j, (y i j) ^ 2 = 1) (a : κ → ℕ) (L : ℕ) (hL : 0 < L)
    (hbin : ∀ j i, ((a j : ℝ) / L) ^ 2 ≤ y i j ∧
      y i j ≤ (((a j : ℝ) + 1) / L) ^ 2) :
    let u : κ → ℝ := fun j => Real.sqrt (∑ i, w i * (y i j) ^ 2)
    let D : (κ → ℝ) → Matrix κ κ ℂ := fun v => diagonal (fun j => (v j : ℂ))
    traceNorm (D u * C * D u - ∑ i, w i • (D (y i) * C * D (y i))) ≤
      2 * Real.sqrt (Fintype.card κ : ℝ) / (L : ℝ) ^ 2 := by
  intro u D
  calc
    _ ≤ 4 * Real.sqrt (∑ j, (u j - ∑ i, w i * y i j) ^ 2) := by
      simpa only [posteriorFactor_gram C hC, D] using
        traceNorm_posteriorBenchmark_sub_le C hC hdiag w y hw hsum hy
    _ ≤ 4 * Real.sqrt ((Fintype.card κ : ℝ) * (1 / (2 * (L : ℝ) ^ 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (PetzPosteriorBin.weighted_square_bin_vector_sq_le w y hw hsum
          a L hL hbin)) (by norm_num)
    _ = _ := by
      have hLr : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
      field_simp [hLr]; ring

end D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorBenchmark
