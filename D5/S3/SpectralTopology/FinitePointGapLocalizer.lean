/- GID: D5/S3/SpectralTopology/FinitePointGapLocalizer
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/FinitePointGapLocalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite point-gap certificate gives an explicit two-sided inverse for the zero-scale Hermitian localizer. -/

import D5.S3.SpectralTopology.FiniteHermitianLocalizer
import Mathlib.Tactic

/-!
# Finite point-gap localizer

A point gap at `z` is recorded by an explicit two-sided inverse of `H-zI`.
From that certificate, the zero-scale Hermitian localizer has the explicit
inverse with the inverse and its conjugate transpose in the opposite
off-diagonal blocks. Thus non-Hermitian point-gap invertibility is transported
to ordinary Hermitian block invertibility by a finite algebraic construction.

The file provides the forward certificate and its exact inverse equations. It
does not assert a bulk topological classification, a homotopy invariant, or
an infinite-volume point-gap theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.SpectralTopology.FinitePointGapLocalizer

open D5.S3.SpectralTopology.FiniteHermitianLocalizer

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Explicit finite point-gap certificate for `H-zI`. -/
structure PointGapCertificate
    (H : Matrix n n ℂ) (z : ℂ) where
  inverse : Matrix n n ℂ
  mul_inverse : centeredOperator H z * inverse = 1
  inverse_mul : inverse * centeredOperator H z = 1

/-- Existence of an explicit two-sided point-gap inverse. -/
def HasPointGap (H : Matrix n n ℂ) (z : ℂ) : Prop :=
  Nonempty (PointGapCertificate H z)

/-- An invertible centred operator yields a point-gap certificate. -/
theorem hasPointGap_of_isUnit
    {H : Matrix n n ℂ} {z : ℂ}
    (hUnit : IsUnit (centeredOperator H z)) :
    HasPointGap H z := by
  rcases hUnit with ⟨unit, hUnit⟩
  subst hUnit
  exact ⟨
    { inverse := (↑(unit⁻¹) : Matrix n n ℂ)
      mul_inverse := by simp
      inverse_mul := by simp }⟩

/-- A point-gap certificate makes the centred operator a unit. -/
theorem centeredOperator_isUnit_of_hasPointGap
    {H : Matrix n n ℂ} {z : ℂ}
    (hGap : HasPointGap H z) :
    IsUnit (centeredOperator H z) := by
  rcases hGap with ⟨certificate⟩
  exact isUnit_iff_exists_inv.mpr
    ⟨certificate.inverse, certificate.mul_inverse,
      certificate.inverse_mul⟩

/-- Point-gap certificates are equivalent to ordinary matrix units. -/
theorem hasPointGap_iff_isUnit
    (H : Matrix n n ℂ) (z : ℂ) :
    HasPointGap H z ↔ IsUnit (centeredOperator H z) := by
  exact ⟨centeredOperator_isUnit_of_hasPointGap,
    hasPointGap_of_isUnit⟩

/-- Explicit inverse candidate for the zero-scale localizer. -/
def zeroScaleLocalizerInverse
    {H : Matrix n n ℂ} {z : ℂ}
    (certificate : PointGapCertificate H z) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 certificate.inverseᴴ certificate.inverse 0

private theorem star_mul_inverse
    {H : Matrix n n ℂ} {z : ℂ}
    (certificate : PointGapCertificate H z) :
    (centeredOperator H z)ᴴ * certificate.inverseᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, certificate.inverse_mul]
  simp

private theorem inverse_star_mul
    {H : Matrix n n ℂ} {z : ℂ}
    (certificate : PointGapCertificate H z) :
    certificate.inverseᴴ * (centeredOperator H z)ᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, certificate.mul_inverse]
  simp

/-- The explicit block inverse cancels the zero-scale localizer on the right. -/
theorem zeroScaleLocalizer_mul_inverse
    (X : Matrix n n ℂ) (x : ℝ)
    {H : Matrix n n ℂ} {z : ℂ}
    (certificate : PointGapCertificate H z) :
    finiteHermitianLocalizer X H x z 0 *
        zeroScaleLocalizerInverse certificate = 1 := by
  rw [finiteHermitianLocalizer_zero_scale]
  unfold zeroScaleLocalizerInverse
  rw [Matrix.fromBlocks_multiply]
  rw [certificate.mul_inverse, star_mul_inverse]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply]

/-- The explicit block inverse cancels the zero-scale localizer on the left. -/
theorem inverse_mul_zeroScaleLocalizer
    (X : Matrix n n ℂ) (x : ℝ)
    {H : Matrix n n ℂ} {z : ℂ}
    (certificate : PointGapCertificate H z) :
    zeroScaleLocalizerInverse certificate *
        finiteHermitianLocalizer X H x z 0 = 1 := by
  rw [finiteHermitianLocalizer_zero_scale]
  unfold zeroScaleLocalizerInverse
  rw [Matrix.fromBlocks_multiply]
  rw [inverse_star_mul, certificate.inverse_mul]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply]

/-- Every finite point gap produces an invertible zero-scale Hermitian
localizer. -/
theorem zeroScaleLocalizer_isUnit_of_hasPointGap
    (X : Matrix n n ℂ) (x : ℝ)
    {H : Matrix n n ℂ} {z : ℂ}
    (hGap : HasPointGap H z) :
    IsUnit (finiteHermitianLocalizer X H x z 0) := by
  rcases hGap with ⟨certificate⟩
  exact isUnit_iff_exists_inv.mpr
    ⟨zeroScaleLocalizerInverse certificate,
      zeroScaleLocalizer_mul_inverse X x certificate,
      inverse_mul_zeroScaleLocalizer X x certificate⟩

/-- The explicit inverse also proves nonvanishing of the localizer whenever
the index type is nonempty. -/
theorem zeroScaleLocalizer_ne_zero_of_hasPointGap
    [Nonempty n]
    (X : Matrix n n ℂ) (x : ℝ)
    {H : Matrix n n ℂ} {z : ℂ}
    (hGap : HasPointGap H z) :
    finiteHermitianLocalizer X H x z 0 ≠ 0 := by
  exact (zeroScaleLocalizer_isUnit_of_hasPointGap X x hGap).ne_zero

example : HasPointGap (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  apply hasPointGap_of_isUnit
  simp [centeredOperator]

#print axioms hasPointGap_iff_isUnit
#print axioms zeroScaleLocalizer_mul_inverse
#print axioms inverse_mul_zeroScaleLocalizer
#print axioms zeroScaleLocalizer_isUnit_of_hasPointGap
#print axioms zeroScaleLocalizer_ne_zero_of_hasPointGap

end

end D5.S3.SpectralTopology.FinitePointGapLocalizer
