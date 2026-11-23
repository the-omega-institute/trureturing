/- GID: D5/S3/Quantum/Divergence/PositiveReferenceReplacement
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/PositiveReferenceReplacement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive reference replacement with the exact Klein and logarithmic remainders. -/

import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-! The block replacement identity splits the loss into scaling, a Klein
remainder and a positive logarithm pairing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.PositiveReferenceReplacement

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma le_trace_smul_one {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A ≤ A.trace.re • (1 : Matrix n n ℂ) := by
  let H : HermitianMat n ℂ := ⟨A, hA.isHermitian⟩
  have hH : 0 ≤ H := HermitianMat.zero_le_iff.mpr hA
  have h := HermitianMat.le_trace_smul_one hH
  change A ≤ A.trace.re • (1 : Matrix n n ℂ) at h
  exact h

private def D (X Y : Matrix n n ℂ) : ℝ :=
  (X * (CFC.log X - CFC.log Y)).trace.re

set_option maxHeartbeats 1000000 in
/-- Moving the scalar block of mass `a` into the normalized retained reference
has an exact loss identity. Both subtracted remainders are nonnegative, and the
Klein remainder is bounded below by the stated Hilbert–Schmidt term. -/
theorem positive_reference_replacement [Nonempty n] (C F : Matrix n n ℂ)
    (lam u a : ℝ) (hC : C.PosDef) (hlam : 0 < lam) (hu : 0 < u) (ha : 0 < a)
    (hlo : u • C ≤ F) :
    let b := C.trace.re
    let c := b + lam
    let τ := b⁻¹ • C
    let F' := F + a • τ
    let C' := c • τ
    let t := F.trace.re + a
    let K := D F' F - a
    let E := (τ * (CFC.log F - CFC.log (u • C))).trace.re
    let bound := a * (Real.log (a / (lam * u)) - 1) + t * Real.log (c / b)
    D F C + a * Real.log (a / lam) - D F' C' = bound - K - a * E ∧
      ((a • τ)ᴴ * (a • τ)).trace.re / (2 * t) ≤ K ∧ 0 ≤ E ∧
      D F C + a * Real.log (a / lam) - D F' C' ≤
        bound - ((a • τ)ᴴ * (a • τ)).trace.re / (2 * t) := by
  intro b c τ F' C' t K E bound
  have hb : 0 < b :=
    (Complex.pos_iff.mp (hC.trace_pos)).1
  have hc : 0 < c := add_pos hb hlam
  have hF : F.PosDef := ((hC.smul hu).isStrictlyPositive.of_le hlo).posDef
  have hτ : τ.PosDef := hC.smul (inv_pos.mpr hb)
  have hle : F ≤ F' := le_add_of_nonneg_right (smul_nonneg ha.le hτ.posSemidef.nonneg)
  have hF' : F'.PosDef := (hF.isStrictlyPositive.of_le hle).posDef
  have hτtr : τ.trace.re = 1 := by
    change (b⁻¹ • C).trace.re = 1
    rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, inv_mul_cancel₀ hb.ne']
  have htr : F'.trace.re = t := by
    simp [F', t, Matrix.trace_add, Matrix.trace_smul, hτtr]
  have ht : 0 < t := by
    rw [← htr]
    exact (Complex.pos_iff.mp (hF'.trace_pos)).1
  have hcap : F' ≤ (t : ℂ) • (1 : Matrix n n ℂ) := by
    have h := le_trace_smul_one hF'.posSemidef
    rw [htr] at h
    have hs : (t : ℂ) • (1 : Matrix n n ℂ) = t • (1 : Matrix n n ℂ) := by
      ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    rwa [hs]
  have hK := SpectralCeilingRelativeEntropy.actual_matrix_spectral_ceiling_strong_klein
    F' F hF'.posSemidef hF.posSemidef t ht hcap (hle.trans hcap) (by
      intro w hw
      have : w = 0 := hF.mulVec_injective (by simpa using hw)
      simp [this])
  change _ ≤ D F' F - F'.trace.re + F.trace.re at hK
  rw [show F' - F = a • τ by simp [F'], htr, show t = F.trace.re + a from rfl] at hK
  have hK' : ((a • τ)ᴴ * (a • τ)).trace.re / (2 * t) ≤ K := by
    dsimp only [K]
    linarith only [hK]
  have hE : 0 ≤ E :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hτ.posSemidef
      (Matrix.le_iff.mp (CFC.log_le_log hlo (hC.smul hu).isStrictlyPositive))
  have hlogC' : CFC.log C' = Real.log (c / b) • (1 : Matrix n n ℂ) + CFC.log C := by
    change CFC.log (c • (b⁻¹ • C)) = _
    rw [smul_smul, ← div_eq_mul_inv, CFC.log_smul' C (div_pos hc hb) hC.isStrictlyPositive]
    rw [Algebra.algebraMap_eq_smul_one]
  have hlogu : CFC.log (u • C) = Real.log u • (1 : Matrix n n ℂ) + CFC.log C := by
    rw [CFC.log_smul' C hu hC.isStrictlyPositive, Algebra.algebraMap_eq_smul_one]
  have hlog : Real.log (a / (lam * u)) = Real.log (a / lam) - Real.log u := by
    rw [← div_div, Real.log_div (div_pos ha hlam).ne' hu.ne']
  have heq : D F C + a * Real.log (a / lam) - D F' C' = bound - K - a * E := by
    dsimp only [bound, K, E, D]
    rw [hlogC', hlogu, hlog]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add,
      Complex.sub_re, Complex.add_re, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul, hτtr]
    have expand (X : Matrix n n ℂ) : (F' * X).trace.re =
        (F * X).trace.re + a * (τ * X).trace.re := by
      simp [F', Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul]
    rw [expand (CFC.log C), expand (CFC.log F), htr]
    ring
  refine ⟨heq, hK', hE, ?_⟩
  rw [heq]
  linarith [mul_nonneg ha.le hE]

#print axioms positive_reference_replacement

end D5.S3.Quantum.Divergence.PositiveReferenceReplacement
