import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation

/-!
# Trace error at the ordinary Petz boundary

Schatten Hölder controls the difference of the two Gram products. The
two-sided spectral evaluation bound then controls the squared trace error
of the zero-rotation output using the upper-boundary integral.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability (entryNormSq_eq_hs_sq)
open PetzExponentialBoundaryEvaluation

namespace PetzBoundaryTraceConsumer

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem traceNorm_mul_le_frobenius (X Y : Matrix n n ℂ) :
    traceNorm (X * Y) ≤ ‖X‖ * ‖Y‖ := by
  simpa only [entryNormSq_eq_hs_sq, Real.sqrt_sq_eq_abs, abs_norm] using
    D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq X Y

/-- The trace-norm difference of two Gram products is controlled by the
Hilbert–Schmidt difference of the amplitudes. -/
theorem traceNorm_gram_sub_le (A B : Matrix n n ℂ) :
    traceNorm (B * Bᴴ - A * Aᴴ) ≤ (‖A‖ + ‖B‖) * ‖B - A‖ := by
  calc
    traceNorm (B * Bᴴ - A * Aᴴ) =
        traceNorm ((B - A) * Bᴴ + A * (Bᴴ - Aᴴ)) := by
      congr 1
      noncomm_ring
    _ ≤ traceNorm ((B - A) * Bᴴ) + traceNorm (A * (Bᴴ - Aᴴ)) :=
      traceNorm_add_le _ _
    _ ≤ ‖B - A‖ * ‖Bᴴ‖ + ‖A‖ * ‖Bᴴ - Aᴴ‖ :=
      add_le_add (traceNorm_mul_le_frobenius _ _) (traceNorm_mul_le_frobenius _ _)
    _ = (‖A‖ + ‖B‖) * ‖B - A‖ := by
      rw [← Matrix.conjTranspose_sub B A]
      simp only [Matrix.frobenius_norm_conjTranspose]
      ring

/-- The Gram-product bridge for unit Hilbert–Schmidt amplitudes. -/
theorem traceNorm_gram_sub_le_two (A B : Matrix n n ℂ)
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) :
    traceNorm (B * Bᴴ - A * Aᴴ) ≤ 2 * ‖B - A‖ := by
  calc
    _ ≤ (‖A‖ + ‖B‖) * ‖B - A‖ := traceNorm_gram_sub_le A B
    _ = _ := by norm_num [hA, hB]

/-- The squared Gram output error at zero rotation is bounded by
`8(d²+1)` times the weighted upper-boundary error integral. -/
theorem traceNorm_gram_sub_sq_le_petz_boundary_dim {β : Type*} [Fintype β]
    (d : ℕ) (block : n → n → β) (outer : β → ℝ) (q p : Fin d → ℝ)
    (A : Matrix n n ℂ) (C : Fin d × Fin d → Matrix n n ℂ)
    (hA : ‖A‖ = 1) (hB : ‖A - petzBoundary block outer q p A C 0‖ = 1) :
    let B := A - petzBoundary block outer q p A C 0
    traceNorm (B * Bᴴ - A * Aᴴ) ^ 2 ≤ (8 * ((d : ℝ) ^ 2 + 1)) *
      (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) := by
  let E := petzBoundary block outer q p A C 0
  let B := A - E
  have hBA : B - A = -E := by
    dsimp only [B]
    abel
  have hTrace : traceNorm (B * Bᴴ - A * Aᴴ) ≤ 2 * ‖E‖ := by
    simpa only [hBA, norm_neg] using traceNorm_gram_sub_le_two A B hA hB
  calc
    traceNorm (B * Bᴴ - A * Aᴴ) ^ 2 ≤ (2 * ‖E‖) ^ 2 :=
      pow_le_pow_left₀ (traceNorm_nonneg _) hTrace 2
    _ = 4 * ‖E‖ ^ 2 := by ring
    _ ≤ 4 * ((2 * ((1 + d ^ 2 : ℕ) : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (weighted_evaluation_petz_boundary_dim d block outer q p A C).2 (by norm_num)
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      ring

end PetzBoundaryTraceConsumer
