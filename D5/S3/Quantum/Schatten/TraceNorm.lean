/- GID: D5/S3/Quantum/Schatten/TraceNorm
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/TraceNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The trace norm as a unitarily invariant norm and its two-dimensional
   determinant formula. -/

import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S0.Observation.MatrixTracePowerSum

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Schatten.TraceNorm
open D5.S3.Quantum.Foundation.FiniteTraceDistance

/-- The trace norm, assembled as a unitarily invariant norm. -/
def traceNormUINorm (n : ℕ) : UINorm n where
  N := traceNorm
  nonneg := traceNorm_nonneg
  eq_zero_iff := by
    intro A
    constructor
    · intro h
      have hp := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
      have hi := (Complex.nonneg_iff.mp hp.trace_nonneg).2
      have hz : (CFC.sqrt (Aᴴ * A)).trace = 0 := Complex.ext h hi.symm
      exact CFC.abs_eq_zero_iff.mp (hp.trace_eq_zero_iff.mp hz)
    · rintro rfl
      simp [traceNorm]
  add_le := traceNorm_add_le
  smul_eq := by
    intro c A
    have h := CFC.abs_smul c A
    change CFC.sqrt ((c • A)ᴴ * (c • A)) = ‖c‖ • CFC.sqrt (Aᴴ * A) at h
    change (CFC.sqrt ((c • A)ᴴ * (c • A))).trace.re =
      ‖c‖ * (CFC.sqrt (Aᴴ * A)).trace.re
    rw [h, Matrix.trace_smul]
    simp [Complex.smul_re]
  unitary_invariant := by
    intro U V A hU hV
    have hle (u v : Matrix.unitaryGroup (Fin n) ℂ)
        (Y : Matrix (Fin n) (Fin n) ℂ) :
        traceNorm (u.val * Y * v.val) ≤ traceNorm Y := by
      obtain ⟨W, hW⟩ := (traceNorm_eq_max_re_tr_U (u.val * Y * v.val)).1
      rw [← hW]
      apply (traceNorm_eq_max_re_tr_U Y).2
      refine ⟨v * W * u, ?_⟩
      simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨U, hU⟩
    let v : Matrix.unitaryGroup (Fin n) ℂ := ⟨V, hV⟩
    apply le_antisymm (hle u v A)
    have h := hle (star u) (star v) (U * A * V)
    have hc : (star u).val * (U * A * V) * (star v).val = A := by
      change Uᴴ * (U * A * V) * Vᴴ = A
      calc
        _ = (Uᴴ * U) * A * (V * Vᴴ) := by simp only [Matrix.mul_assoc]
        _ = A := by
          have hU' : Uᴴ * U = 1 := by
            simpa only [Matrix.star_eq_conjTranspose] using
              Matrix.mem_unitaryGroup_iff'.mp hU
          have hV' : V * Vᴴ = 1 := by
            simpa only [Matrix.star_eq_conjTranspose] using
              Matrix.mem_unitaryGroup_iff.mp hV
          rw [hU', hV']
          simp
    rwa [hc] at h

theorem det_transitionAbs (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (CFC.sqrt (Tᴴ * T)).det = (‖T.det‖ : ℂ) := by
  rw [(posSemidef_conjTranspose_mul_self T).det_sqrt,
    RCLike.sqrt_of_nonneg (posSemidef_conjTranspose_mul_self T).det_nonneg,
    Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [RCLike.re_eq_complex_re, Complex.star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem transitionMass_sq (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (CFC.sqrt (Tᴴ * T)).trace.re ^ 2 = RHLinalg.frobSq T + 2 * ‖T.det‖ := by
  have hr := (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Tᴴ * T))).trace_nonneg).2
  have h := congrArg Complex.re
    (D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two
      (CFC.sqrt (Tᴴ * T)) 0)
  simp only [Nat.zero_add, pow_two, pow_zero, pow_one, Matrix.trace_one] at h
  rw [CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self T).nonneg,
    det_transitionAbs] at h
  norm_num [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, hr.symm, RHLinalg.frobSq,
    RCLike.re_eq_complex_re] at h
  change (CFC.sqrt (Tᴴ * T)).trace.re ^ 2 = (Tᴴ * T).trace.re + 2 * ‖T.det‖
  nlinarith [h]

end D5.S3.Quantum.Schatten.TraceNorm
