/- GID: D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix
   generality: G
   mirror-B: D5/B/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive-mass signed-normal atom has a positive ordinary Hankel matrix and a negative shifted localizing witness exactly off the reflection boundary. -/

import D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Repository searches for `SignedNormalSpectralAtom`,
     `SignedNormalLocalizingMatrix`, and shifted signed-normal Hankel owners
     found research targets in the consolidated RH theory volume but no Lean
     owner.
   * `ReflectedGrowthPairNegativeSquare` already owns the signed location
     `reflectionPairSignedDeterminant delta = -delta^2`; it is imported and
     used directly.
   * `RHLinalg.hermForm` is reused for the finite quadratic readout, and
     Mathlib's positive-semidefinite rank-one outer-product theorem is reused
     for the ordinary Hankel matrix.
   * The construction is a single positive atom. It separates positive mass
     from support location and does not construct the global completed-zeta
     normal spectral measure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace D5.S3.Analytic.ReflectedSpectrum.SignedNormalLocalizingMatrix

open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
open RHLinalg

/-- The signed-normal support coordinate of a reflected split. -/
def signedNormalLocation (delta : ℝ) : ℝ :=
  reflectionPairSignedDeterminant delta

/-- The moment sequence of a single atom of real mass at the signed-normal
location. -/
def signedNormalAtomMoment (mass delta : ℝ) (order : ℕ) : ℝ :=
  mass * signedNormalLocation delta ^ order

/-- Monomials evaluated at the signed-normal support coordinate. -/
def signedNormalMonomialVector (dimension : ℕ) (delta : ℝ) : Fin dimension → ℂ :=
  fun index => (signedNormalLocation delta : ℂ) ^ index.1

/-- The ordinary positive-mass Hankel matrix. It is stored in its rank-one
outer-product factorization. -/
def signedNormalHankelMatrix (dimension : ℕ) (mass delta : ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℂ :=
  (mass : ℝ) • Matrix.vecMulVec
    (signedNormalMonomialVector dimension delta)
    (star (signedNormalMonomialVector dimension delta))

/-- The first shifted localizing matrix. Multiplication by the support
coordinate tests whether the atom lies in the allowed half-line. -/
def signedNormalLocalizingMatrix (dimension : ℕ) (mass delta : ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℂ :=
  (mass * signedNormalLocation delta : ℝ) • Matrix.vecMulVec
    (signedNormalMonomialVector dimension delta)
    (star (signedNormalMonomialVector dimension delta))

/-- The canonical one-coordinate test vector. -/
def unitCoordinateWitness : Fin 1 → ℂ := fun _ => 1

/-- The signed-normal support location is exactly the reflected negative
square. -/
theorem signed_normal_location_eq_neg_sq (delta : ℝ) :
    signedNormalLocation delta = -(delta ^ 2) := by
  exact (reflection_pair_signed_determinant delta 0).2.1

/-- The signed-normal location is strictly negative exactly when the reflected
split is nonzero. -/
theorem signed_normal_location_negative_iff (delta : ℝ) :
    signedNormalLocation delta < 0 ↔ delta ≠ 0 := by
  rw [signed_normal_location_eq_neg_sq]
  constructor
  · intro hnegative hzero
    subst delta
    norm_num at hnegative
  · intro hdelta
    exact neg_neg_iff_pos.mpr (sq_pos_of_ne_zero hdelta)

/-- The zeroth single-atom moment is its mass. -/
theorem signed_normal_atom_moment_zero (mass delta : ℝ) :
    signedNormalAtomMoment mass delta 0 = mass := by
  simp [signedNormalAtomMoment]

/-- Nonnegative atom mass makes every ordinary Hankel truncation positive
semidefinite, independently of the sign of its support location. -/
theorem signed_normal_hankel_posSemidef
    (dimension : ℕ) (mass delta : ℝ) (hmass : 0 ≤ mass) :
    (signedNormalHankelMatrix dimension mass delta).PosSemidef := by
  unfold signedNormalHankelMatrix
  exact (Matrix.posSemidef_vecMulVec_self_star
    (signedNormalMonomialVector dimension delta)).smul hmass

/-- The one-coordinate localizing quadratic readout is mass times the signed
support location. -/
theorem signed_normal_localizing_unit_readout (mass delta : ℝ) :
    hermForm (signedNormalLocalizingMatrix 1 mass delta)
      unitCoordinateWitness = mass * signedNormalLocation delta := by
  simp [signedNormalLocalizingMatrix, signedNormalMonomialVector,
    unitCoordinateWitness, hermForm, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec_apply, Fin.sum_univ_one, Pi.star_apply]

/-- Positive mass at a nonzero reflected split gives a strict negative
localizing witness. -/
theorem signed_normal_localizing_unit_negative
    (mass delta : ℝ) (hmass : 0 < mass) (hdelta : delta ≠ 0) :
    hermForm (signedNormalLocalizingMatrix 1 mass delta)
      unitCoordinateWitness < 0 := by
  rw [signed_normal_localizing_unit_readout]
  exact mul_neg_of_pos_of_neg hmass
    ((signed_normal_location_negative_iff delta).2 hdelta)

/-- A positive-mass off-boundary atom simultaneously has positive ordinary
Hankel truncations and a finite negative support-localizing certificate. -/
theorem signed_normal_atom_hankel_localizing_certificate
    (mass delta : ℝ) (hmass : 0 < mass) (hdelta : delta ≠ 0) :
    (signedNormalHankelMatrix 1 mass delta).PosSemidef ∧
      hermForm (signedNormalLocalizingMatrix 1 mass delta)
        unitCoordinateWitness < 0 := by
  exact ⟨signed_normal_hankel_posSemidef 1 mass delta hmass.le,
    signed_normal_localizing_unit_negative mass delta hmass hdelta⟩

/-- The hypotheses of the support-separation certificate are inhabited. -/
example :
    hermForm (signedNormalLocalizingMatrix 1 1 1)
      unitCoordinateWitness < 0 := by
  exact signed_normal_localizing_unit_negative 1 1 zero_lt_one one_ne_zero

#print axioms signed_normal_location_negative_iff
#print axioms signed_normal_hankel_posSemidef
#print axioms signed_normal_localizing_unit_readout
#print axioms signed_normal_localizing_unit_negative
#print axioms signed_normal_atom_hankel_localizing_certificate

end D5.S3.Analytic.ReflectedSpectrum.SignedNormalLocalizingMatrix
