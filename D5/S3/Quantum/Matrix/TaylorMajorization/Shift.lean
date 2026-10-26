/- GID: D5/S3/Quantum/Matrix/TaylorMajorization/Shift
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/TaylorMajorization/Shift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar translation of ordered matrix Taylor coefficients and their trace defects. -/

import D5.S3.Quantum.Matrix.TaylorMajorization.Defs
import D5.S3.Quantum.Measurement.IncoherentCone

noncomputable section
open Matrix BigOperators Finset
open D5.S3.Quantum.Matrix.TaylorMajorization.Defs

namespace D5.S3.Quantum.Matrix.TaylorMajorization.Shift
variable {n : ℕ}

private theorem operator_formula (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ((LinearMap.mulLeft ℂ A + LinearMap.mulRight ℂ B) ^ k) 1 = taylorQ A B k := by
  rw [(LinearMap.commute_mulLeft_right A B).add_pow' k]
  delta taylorQ
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.pow_mulLeft, LinearMap.pow_mulRight, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, one_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.cast_smul_eq_nsmul]

/-- Scalar translation acts on the ordered Taylor coefficients by a binomial transform. -/
theorem taylorQ_shift (A B : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (k : ℕ) :
    taylorQ (A + s • 1) B k =
      ∑ j ∈ range (k + 1), ((k.choose j : ℂ) * s ^ (k - j)) • taylorQ A B j := by
  let L := LinearMap.mulLeft ℂ A + LinearMap.mulRight ℂ B
  have he : LinearMap.mulLeft ℂ (A + s • 1) + LinearMap.mulRight ℂ B = L + s • 1 := by
    ext C
    simp [L, add_mul, add_right_comm]
  rw [← operator_formula, he, ((Commute.one_right L).smul_right s).add_pow' k]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    smul_pow, one_pow, Module.End.one_apply, map_smul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro j hj
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [← operator_formula, L, smul_smul]

/-- Taking the real trace commutes with Hermitian symmetrization. -/
theorem trace_taylorR (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (taylorR A B k).trace.re = (taylorQ A B k).trace.re := by
  delta taylorR
  simpa [RHLinalg.rtrace, selfAdjointPart_apply_coe, invOf_eq_inv,
    Matrix.star_eq_conjTranspose] using
    (D5.S3.Quantum.Measurement.IncoherentCone.trace_hermitianPart
      (G := (1 : Matrix (Fin n) (Fin n) ℂ)) isHermitian_one (taylorQ A B k))

/-- Scalar translation acts on the real trace defect by the same binomial transform. -/
theorem defect_shift (A B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (k : ℕ) :
    defect (A + (s : ℂ) • 1) B k =
      ∑ j ∈ range (k + 1), (k.choose j : ℝ) * s ^ (k - j) * defect A B j := by
  have he : A + (s : ℂ) • 1 + B = (A + B) + (s : ℂ) • 1 := by abel
  have hp : ((A + B) + (s : ℂ) • 1) ^ k =
      ∑ j ∈ range (k + 1), ((k.choose j : ℂ) * (s : ℂ) ^ (k - j)) • (A + B) ^ j := by
    rw [((Commute.one_right (A + B)).smul_right (s : ℂ)).add_pow' k]
    simp only [Nat.sum_antidiagonal_eq_sum_range_succ_mk, smul_pow, one_pow,
      mul_smul_comm, mul_one, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp only [defect, trace_taylorR, taylorQ_shift, he, hp, trace_sum, trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, ← Complex.ofReal_pow,
    mul_zero, zero_mul, add_zero, sub_zero, sum_sub_distrib, mul_sub]

end D5.S3.Quantum.Matrix.TaylorMajorization.Shift
