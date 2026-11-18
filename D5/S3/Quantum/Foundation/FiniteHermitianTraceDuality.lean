/- GID: D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteHermitianTraceDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian contraction tests control the complex finite trace norm. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Analysis.Complex.Basic

/-! The real and imaginary parts of a unitary are Hermitian contractions. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality

open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped Matrix.Norms.L2Operator ComplexStarModule

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem trace_mul_im_zero (F X : Matrix n n ℂ)
    (hF : F.IsHermitian) (hX : X.IsHermitian) : (Matrix.trace (F * X)).im = 0 := by
  have hc : star (Matrix.trace (F * X)) = Matrix.trace (F * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hF.eq, hX.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- Every Hermitian matrix has an attaining Hermitian contraction test. -/
theorem exists_hermitian_traceNorm_test (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    ∃ F : Matrix n n ℂ, F.IsHermitian ∧ ‖F‖ ≤ 1 ∧
      (Matrix.trace (F * X)).re = traceNorm X := by
  classical
  by_cases hn : Nonempty n
  · letI := hn
    obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U X).1
    let F : Matrix n n ℂ := (realPart U.val : Matrix n n ℂ)
    let G : Matrix n n ℂ := (imaginaryPart U.val : Matrix n n ℂ)
    have hf : F.IsHermitian := (realPart U.val).property
    have hg : G.IsHermitian := (imaginaryPart U.val).property
    refine ⟨F, hf, ?_, ?_⟩
    · change ‖realPart U.val‖ ≤ 1
      exact (realPart.norm_le U.val).trans_eq (CStarRing.norm_coe_unitary U)
    · have he : U.val * X = F * X + Complex.I • (G * X) := by
        conv_lhs => rw [← realPart_add_I_smul_imaginaryPart U.val]
        simp only [Matrix.add_mul, Matrix.smul_mul, F, G]
      rw [he, Matrix.trace_add, Matrix.trace_smul] at hU
      simpa [Complex.add_re, Complex.mul_re, trace_mul_im_zero G X hg hX] using hU
  · haveI : IsEmpty n := not_nonempty_iff.mp hn
    refine ⟨0, by simp, by simp, ?_⟩
    have hx : X = 0 := Subsingleton.elim _ _
    simp [hx, traceNorm]

/-- A uniform bound on all Hermitian contraction tests bounds the trace norm
of a Hermitian matrix without a dimension factor. -/
theorem hermitian_traceNorm_le_tests (X : Matrix n n ℂ) (hX : X.IsHermitian) (m : ℝ)
    (htest : ∀ F : Matrix n n ℂ, F.IsHermitian → ‖F‖ ≤ 1 →
      (Matrix.trace (F * X)).re ≤ m) : traceNorm X ≤ m := by
  obtain ⟨F, hf, hfn, he⟩ := exists_hermitian_traceNorm_test X hX
  rw [← he]
  exact htest F hf hfn

/-- Testing all Hermitian contractions controls a general complex matrix,
with the factor two retained. -/
theorem complex_traceNorm_le_twice_tests (X : Matrix n n ℂ) (m : ℝ)
    (htest : ∀ F : Matrix n n ℂ, F.IsHermitian → ‖F‖ ≤ 1 →
      ‖Matrix.trace (F * X)‖ ≤ m) : traceNorm X ≤ 2 * m := by
  classical
  have hm : 0 ≤ m := by simpa using htest 0 (by simp) (by simp)
  by_cases hn : Nonempty n
  · letI := hn
    obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U X).1
    have hu : ‖U.val‖ = 1 := CStarRing.norm_coe_unitary U
    let F : Matrix n n ℂ := (realPart U.val : Matrix n n ℂ)
    let G : Matrix n n ℂ := (imaginaryPart U.val : Matrix n n ℂ)
    have hf : F.IsHermitian := (realPart U.val).property
    have hg : G.IsHermitian := (imaginaryPart U.val).property
    have hfn : ‖F‖ ≤ 1 := by
      change ‖realPart U.val‖ ≤ 1
      exact (realPart.norm_le U.val).trans_eq hu
    have hgn : ‖G‖ ≤ 1 := by
      change ‖imaginaryPart U.val‖ ≤ 1
      exact (imaginaryPart.norm_le U.val).trans_eq hu
    have he : U.val * X = F * X + Complex.I • (G * X) := by
      conv_lhs => rw [← realPart_add_I_smul_imaginaryPart U.val]
      simp only [Matrix.add_mul, Matrix.smul_mul, F, G]
    calc
      traceNorm X = (Matrix.trace (U.val * X)).re := hU.symm
      _ ≤ ‖Matrix.trace (U.val * X)‖ := Complex.re_le_norm _
      _ = ‖Matrix.trace (F * X) + Complex.I * Matrix.trace (G * X)‖ := by
        rw [he, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      _ ≤ ‖Matrix.trace (F * X)‖ + ‖Complex.I * Matrix.trace (G * X)‖ := norm_add_le _ _
      _ = ‖Matrix.trace (F * X)‖ + ‖Matrix.trace (G * X)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ m + m := add_le_add (htest F hf hfn) (htest G hg hgn)
      _ = 2 * m := by ring
  · haveI : IsEmpty n := not_nonempty_iff.mp hn
    have hx : X = 0 := Subsingleton.elim _ _
    rw [hx]
    simpa [traceNorm] using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)

end D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality
