/- GID: D5/S3/QuantumStates/GNSZeroPropagation
   generality: G
   mirror-B: D5/B/S3/QuantumStates/GNSZeroPropagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive matrix functional has the zero-norm propagation property. -/

import D5.S3.Quantum.GNSMatrix

namespace D5.S3.QuantumStates.GNSZeroPropagation

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open Matrix

/- The functional is built from the source weight matrix and is not defined by the target. -/
noncomputable def stateFunctional {d : Type*} [Fintype d]
    (rho : Matrix d d ℂ) (a : Matrix d d ℂ) : ℂ :=
  Matrix.trace (rho * a)

private theorem cross_trace_factorization {d : Type*} [Fintype d] [DecidableEq d]
    (rho h g : Matrix d d ℂ) (hRho : rho.PosSemidef) :
    stateFunctional rho (hᴴ * g) =
      Matrix.trace ((h * CFC.sqrt rho)ᴴ * (g * CFC.sqrt rho)) := by
  have hSqrtSq : CFC.sqrt rho * CFC.sqrt rho = rho :=
    CFC.sqrt_mul_sqrt_self rho hRho.nonneg
  have hSqrtStar : (CFC.sqrt rho)ᴴ = CFC.sqrt rho := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg rho).isSelfAdjoint.star_eq
  calc
    stateFunctional rho (hᴴ * g) = Matrix.trace (rho * (hᴴ * g)) := rfl
    _ = Matrix.trace (CFC.sqrt rho * CFC.sqrt rho * (hᴴ * g)) := by
      rw [hSqrtSq]
    _ = Matrix.trace (CFC.sqrt rho * (hᴴ * g) * CFC.sqrt rho) :=
      (Matrix.trace_mul_cycle (CFC.sqrt rho) (hᴴ * g) (CFC.sqrt rho)).symm
    _ = Matrix.trace ((h * CFC.sqrt rho)ᴴ * (g * CFC.sqrt rho)) := by
      simp only [Matrix.conjTranspose_mul, hSqrtStar, Matrix.mul_assoc]

/-- A positive normalized matrix functional propagates a zero quadratic value to every
mixed value with the same right argument. -/
theorem gns_zero_norm_propagation {d : Type*} [Fintype d] [DecidableEq d]
    (rho g : Matrix d d ℂ) (hRho : rho.PosSemidef)
    (hTrace : Matrix.trace rho = 1)
    (hZero : stateFunctional rho (gᴴ * g) = 0) :
    ∀ h', stateFunctional rho (h'ᴴ * g) = 0 := by
  intro h'
  have hSquare := D5.S3.Quantum.GNSMatrix.gns_matrix_identity rho g hRho hTrace
  have hZero' : Matrix.trace (rho * gᴴ * g) = 0 := by
    rw [Matrix.mul_assoc]
    simpa [stateFunctional] using hZero
  have hNormComplex : (‖g * CFC.sqrt rho‖ : ℂ) ^ 2 = 0 := by
    rw [← hSquare]
    exact hZero'
  have hNormSq : (‖g * CFC.sqrt rho‖ : ℝ) ^ 2 = 0 := by
    exact_mod_cast hNormComplex
  have hNorm : ‖g * CFC.sqrt rho‖ = 0 := by
    exact sq_eq_zero_iff.mp hNormSq
  have hProduct : g * CFC.sqrt rho = 0 := norm_eq_zero.mp hNorm
  rw [cross_trace_factorization rho h' g hRho]
  simp [hProduct]

#print axioms gns_zero_norm_propagation

end D5.S3.QuantumStates.GNSZeroPropagation
