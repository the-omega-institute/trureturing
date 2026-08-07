/- GID: D5/S3/Quantum/MatrixInversion
   generality: G
   mirror-B: D5/B/S3/Quantum/MatrixInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor weighted inverses and invert the associated affine matrix segment. -/

import Mathlib

namespace D5.S3.Quantum.MatrixInversion

open scoped ComplexOrder

/-- Weighted inverses of positive-definite matrices factor in the stated order
for arbitrary real weights. -/
theorem weighted_inverse_factorization
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef)
    (a b : ℝ) :
    a • rho⁻¹ + b • sigma⁻¹ =
      rho⁻¹ * (a • sigma + b • rho) * sigma⁻¹ := by
  have hRhoDet : IsUnit rho.det :=
    (Matrix.isUnit_iff_isUnit_det rho).mp hRho.isUnit
  have hSigmaDet : IsUnit sigma.det :=
    (Matrix.isUnit_iff_isUnit_det sigma).mp hSigma.isUnit
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv sigma hSigmaDet,
    Matrix.nonsing_inv_mul rho hRhoDet, Matrix.mul_one, Matrix.one_mul]

/-- The inverse of an affine weighted inverse sum reverses the factor order. -/
theorem affine_inverse_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - u) • rho⁻¹ + u • sigma⁻¹)⁻¹ =
      sigma * ((1 - u) • sigma + u • rho)⁻¹ * rho := by
  have hRhoDet : IsUnit rho.det :=
    (Matrix.isUnit_iff_isUnit_det rho).mp hRho.isUnit
  have hSigmaDet : IsUnit sigma.det :=
    (Matrix.isUnit_iff_isUnit_det sigma).mp hSigma.isUnit
  have hSegment : ((1 - u) • sigma + u • rho).PosDef := by
    rcases hu with ⟨huNonnegative, huAtMostOne⟩
    by_cases huOne : u = 1
    · subst u
      simpa using hRho
    · exact (hSigma.smul (sub_pos.mpr (lt_of_le_of_ne huAtMostOne huOne))).add_posSemidef
        (hRho.posSemidef.smul huNonnegative)
  have hSegmentDet : IsUnit ((1 - u) • sigma + u • rho).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSegment.isUnit
  rw [weighted_inverse_factorization rho sigma hRho hSigma (1 - u) u]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_assoc sigma (((1 - u) • sigma + u • rho)⁻¹) rho,
    ← Matrix.mul_assoc
      (rho⁻¹ * ((1 - u) • sigma + u • rho) * sigma⁻¹) sigma
      (((1 - u) • sigma + u • rho)⁻¹ * rho),
    Matrix.mul_assoc (rho⁻¹ * ((1 - u) • sigma + u • rho)) sigma⁻¹ sigma,
    Matrix.nonsing_inv_mul sigma hSigmaDet, Matrix.mul_one,
    ← Matrix.mul_assoc (rho⁻¹ * ((1 - u) • sigma + u • rho))
      (((1 - u) • sigma + u • rho)⁻¹) rho,
    Matrix.mul_assoc rho⁻¹ ((1 - u) • sigma + u • rho)
      (((1 - u) • sigma + u • rho)⁻¹),
    Matrix.mul_nonsing_inv _ hSegmentDet, Matrix.mul_one,
    Matrix.nonsing_inv_mul rho hRhoDet]

/-- Source-faithful combined statement retained for the deposited GID. -/
theorem positive_definite_inversion_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : Matrix n n ℂ) (hRho : rho.PosDef) (hSigma : sigma.PosDef)
    (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (a • rho⁻¹ + b • sigma⁻¹ =
      rho⁻¹ * (a • sigma + b • rho) * sigma⁻¹) ∧
    ((1 - u) • rho⁻¹ + u • sigma⁻¹)⁻¹ =
      sigma * ((1 - u) • sigma + u • rho)⁻¹ * rho := by
  exact ⟨weighted_inverse_factorization rho sigma hRho hSigma a b,
    affine_inverse_identity rho sigma hRho hSigma u hu⟩

end D5.S3.Quantum.MatrixInversion
