/- GID: D5/S3/Midline/Cayley/CanonicalZetaCayleyJUnitary
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/CanonicalZetaCayleyJUnitary
   mirror-E: none(waiver:canonical-zeta-krein-interface)
   anchors: []
   digest: Prove the zero Cayley operator unconditionally preserves the indefinite inner product induced by same-height reflection. -/

import D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
import D5.S3.Midline.Cayley.CayleyMirrorCoordinates

/-!
# The zeta-zero Cayley operator is mirror `J`-unitary

The Cayley coefficient at a same-height reflected zero is the reciprocal of
the conjugate coefficient.  On the multiplicity-expanded zero Hilbert space,
this is exactly the coordinate identity needed for the diagonal Cayley
operator to preserve the mirror indefinite inner product.

Thus functional-equation symmetry yields `J`-unitarity without RH.  Ordinary
unitarity is the stronger critical-line condition treated by the existing
Cayley unitarity criterion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.CanonicalZetaCayleyJUnitary

open D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open D5.S3.Midline.Cayley.CayleyUnitarityDefect
open D5.S3.Midline.Cayley.CayleyMirrorCoordinates
open D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity
open D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
open D5.S3.Weil.ReflectionLedger
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
open D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData
open scoped ComplexConjugate ENNReal InnerProduct lp

private theorem zero_ne_zero (Z : ZeroData) (n : ℕ) : Z.zero n ≠ 0 := by
  intro hzero
  have hpositive := (Z.zero_isNontrivial n).2.1
  rw [hzero] at hpositive
  norm_num at hpositive

private theorem zero_ne_one (Z : ZeroData) (n : ℕ) : Z.zero n ≠ 1 := by
  intro hone
  have hless := (Z.zero_isNontrivial n).2.2
  rw [hone] at hless
  norm_num at hless

private theorem cayleyCoefficient_ne_zero (Z : ZeroData) (n : ℕ) :
    cayleyCoefficient (Z.zero n) ≠ 0 := by
  rw [cayleyCoefficient]
  exact div_ne_zero (sub_ne_zero.mpr (zero_ne_one Z n)) (zero_ne_zero Z n)

/-- Same-height reflection sends a zero Cayley coefficient to the reciprocal
of its conjugate. -/
theorem cayleyCoefficient_mirrorIndex (Z : ZeroData) (n : ℕ) :
    cayleyCoefficient (Z.zero (mirrorIndex Z n)) =
      (conj (cayleyCoefficient (Z.zero n)))⁻¹ := by
  rw [mirrorIndex_zero]
  simpa [mirror, reflection] using
    (cayley_mirror_coordinates (Z.zero n)).1

/-- The two mirror coefficients have the exact product required by the Krein
metric. -/
theorem cayleyCoefficient_conj_mul_mirror (Z : ZeroData) (n : ℕ) :
    conj (cayleyCoefficient (Z.zero n)) *
      cayleyCoefficient (Z.zero (mirrorIndex Z n)) = 1 := by
  rw [cayleyCoefficient_mirrorIndex]
  apply mul_inv_cancel₀
  simpa using cayleyCoefficient_ne_zero Z n

/-- Pointwise scalar multiplication by the two mirror Cayley coefficients
preserves the complex inner product. -/
theorem cayley_mirror_pointwise_inner (Z : ZeroData) (n : ℕ)
    (x y : Complex) :
    ⟪cayleyCoefficient (Z.zero n) * x,
      cayleyCoefficient (Z.zero (mirrorIndex Z n)) * y⟫_Complex =
      ⟪x, y⟫_Complex := by
  change ⟪cayleyCoefficient (Z.zero n) • x,
      cayleyCoefficient (Z.zero (mirrorIndex Z n)) • y⟫_Complex = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc,
    cayleyCoefficient_conj_mul_mirror, one_mul]

/-- The zero Cayley operator preserves the mirror indefinite inner product. -/
theorem zeroCayleyOperator_preserves_mirrorKreinForm (Z : ZeroData)
    (psi phi : MirrorZeroHilbertSpace Z) :
    mirrorKreinForm Z (zeroCayleyOperator Z psi)
        (zeroCayleyOperator Z phi) =
      mirrorKreinForm Z psi phi := by
  rw [mirrorKreinForm, mirrorKreinForm, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro v
  rw [zeroCayleyOperator_apply, mirrorFundamentalSymmetry_apply,
    zeroCayleyOperator_apply]
  exact cayley_mirror_pointwise_inner Z v.1 (psi v)
    (phi (mirrorCoordinatePerm Z v))

/-- Operator form of mirror `J`-unitarity: `U* J U = J`. -/
theorem zeroCayleyOperator_j_unitary (Z : ZeroData) :
    star (zeroCayleyOperator Z) *
        (mirrorFundamentalSymmetry Z :
          MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) *
        zeroCayleyOperator Z =
      (mirrorFundamentalSymmetry Z :
        MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) := by
  apply ContinuousLinearMap.ext
  intro psi
  apply ext_inner_left Complex
  intro phi
  change ⟪phi,
      star (zeroCayleyOperator Z)
        (mirrorFundamentalSymmetry Z (zeroCayleyOperator Z psi))⟫_Complex =
    ⟪phi, mirrorFundamentalSymmetry Z psi⟫_Complex
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact zeroCayleyOperator_preserves_mirrorKreinForm Z phi psi

/-- The parameter-free zeta-zero Cayley operator is unconditionally
`J`-unitary for the canonical mirror symmetry. -/
theorem zetaZeroCayleyOperator_j_unitary :
    star (zeroCayleyOperator zetaZeroData) *
        (zetaMirrorFundamentalSymmetry :
          MirrorZeroHilbertSpace zetaZeroData →L[Complex]
            MirrorZeroHilbertSpace zetaZeroData) *
        zeroCayleyOperator zetaZeroData =
      (zetaMirrorFundamentalSymmetry :
        MirrorZeroHilbertSpace zetaZeroData →L[Complex]
          MirrorZeroHilbertSpace zetaZeroData) := by
  exact zeroCayleyOperator_j_unitary zetaZeroData

#print axioms cayleyCoefficient_mirrorIndex
#print axioms zeroCayleyOperator_preserves_mirrorKreinForm
#print axioms zeroCayleyOperator_j_unitary
#print axioms zetaZeroCayleyOperator_j_unitary

end D5.S3.Midline.Cayley.CanonicalZetaCayleyJUnitary
