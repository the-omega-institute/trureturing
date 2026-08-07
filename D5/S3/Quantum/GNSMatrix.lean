/- GID: D5/S3/Quantum/GNSMatrix
   generality: G
   mirror-B: D5/B/S3/Quantum/GNSMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relate positive trace-one matrix weights to Hilbert-Schmidt norm squares. -/

import Mathlib

namespace D5.S3.Quantum.GNSMatrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open Matrix

private theorem frobenius_norm_sq_eq_trace {d : Type*} [Fintype d]
    (A : Matrix d d ℂ) :
    ((‖A‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (Aᴴ * A) := by
  have hNorm : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))‖ ^ 2 = _
    simp [PiLp.norm_sq_eq_of_L2]
  rw [hNorm, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_pow, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_mul']
  rw [Finset.sum_comm]

/-- A positive trace-one matrix evaluates `xᴴ * x` as a Hilbert-Schmidt norm square. -/
theorem gns_matrix_identity {d : Type*} [Fintype d] [DecidableEq d]
    (rho x : Matrix d d ℂ) (hRho : rho.PosSemidef)
    (_hTrace : Matrix.trace rho = 1) :
    Matrix.trace (rho * xᴴ * x) = (‖x * CFC.sqrt rho‖ : ℂ) ^ 2 := by
  have hSqrtSq : CFC.sqrt rho * CFC.sqrt rho = rho :=
    CFC.sqrt_mul_sqrt_self rho hRho.nonneg
  have hSqrtStar : (CFC.sqrt rho)ᴴ = CFC.sqrt rho := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg rho).isSelfAdjoint.star_eq
  calc
    Matrix.trace (rho * xᴴ * x) =
        Matrix.trace (CFC.sqrt rho * CFC.sqrt rho * (xᴴ * x)) := by
      rw [hSqrtSq, Matrix.mul_assoc]
    _ = Matrix.trace (CFC.sqrt rho * (xᴴ * x) * CFC.sqrt rho) :=
      (Matrix.trace_mul_cycle (CFC.sqrt rho) (xᴴ * x) (CFC.sqrt rho)).symm
    _ = Matrix.trace ((x * CFC.sqrt rho)ᴴ * (x * CFC.sqrt rho)) := by
      simp only [Matrix.conjTranspose_mul, hSqrtStar, Matrix.mul_assoc]
    _ = (‖x * CFC.sqrt rho‖ : ℂ) ^ 2 := by
      simpa only [Complex.ofReal_pow] using
        (frobenius_norm_sq_eq_trace (x * CFC.sqrt rho)).symm

end D5.S3.Quantum.GNSMatrix
