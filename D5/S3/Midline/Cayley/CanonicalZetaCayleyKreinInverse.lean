/- GID: D5/S3/Midline/Cayley/CanonicalZetaCayleyKreinInverse
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/CanonicalZetaCayleyKreinInverse
   mirror-E: none(waiver:canonical-zeta-krein-interface)
   anchors: []
   digest: Construct the unconditional bounded inverse of the zero Cayley operator and identify it with J U-star J. -/

import D5.S3.Midline.Cayley.CanonicalZetaMirrorEvenOddDecomposition
import D5.S3.Midline.Cayley.CanonicalZetaCayleyJUnitary

/-!
# The explicit Krein inverse of the zero Cayley operator

Mirror symmetry makes the reciprocal Cayley coefficient at one coordinate the
complex conjugate of the Cayley coefficient at its mirror coordinate.  Since
the original coefficient vector is bounded, this gives boundedness of the
reciprocal vector without a new analytic estimate.

The corresponding diagonal operator is proved to be a two-sided inverse.  It
is then identified with `J U* J`, yielding the Krein inverse formula and the
companion identity `U J U* = J` without assuming ordinary unitarity or RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.CanonicalZetaCayleyKreinInverse

open D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open D5.S3.Midline.Cayley.CayleyUnitarityDefect
open D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity
open D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
open D5.S3.Midline.Cayley.CanonicalZetaMirrorEvenOddDecomposition
open D5.S3.Midline.Cayley.CanonicalZetaCayleyJUnitary
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

private theorem zero_cayley_coefficient_ne_zero (Z : ZeroData) (n : ℕ) :
    cayleyCoefficient (Z.zero n) ≠ 0 := by
  rw [cayleyCoefficient]
  exact div_ne_zero (sub_ne_zero.mpr (zero_ne_one Z n))
    (zero_ne_zero Z n)

/-- The reciprocal coefficient at an index is the conjugate coefficient at
its same-height mirror. -/
theorem cayleyCoefficient_inv_eq_conj_mirrorIndex (Z : ZeroData) (n : ℕ) :
    (cayleyCoefficient (Z.zero n))⁻¹ =
      conj (cayleyCoefficient (Z.zero (mirrorIndex Z n))) := by
  have h := congrArg conj (cayleyCoefficient_mirrorIndex Z n)
  simpa using h.symm

private theorem inverse_cayley_coefficients_memℓp_infty (Z : ZeroData) :
    Memℓp
      (fun v : ZeroCoordinate Z =>
        (cayleyCoefficient (Z.zero v.1))⁻¹) ∞ := by
  rw [memℓp_infty_iff]
  obtain ⟨C, hC⟩ :=
    (memℓp_infty_iff.mp (cayleyCoefficientVector Z).2)
  refine ⟨C, ?_⟩
  rintro _ ⟨v, rfl⟩
  rw [cayleyCoefficient_inv_eq_conj_mirrorIndex, norm_conj]
  simpa only [cayleyCoefficientVector_apply,
    mirrorCoordinatePerm_fst] using
    hC ⟨mirrorCoordinatePerm Z v, rfl⟩

/-- The bounded reciprocal Cayley coefficient vector. -/
noncomputable def inverseCayleyCoefficientVector (Z : ZeroData) :
    lp (fun _ : ZeroCoordinate Z => Complex) ∞ :=
  ⟨fun v => (cayleyCoefficient (Z.zero v.1))⁻¹,
    inverse_cayley_coefficients_memℓp_infty Z⟩

/-- The diagonal bounded inverse candidate. -/
noncomputable def zeroCayleyInverseOperator (Z : ZeroData) :
    MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z :=
  diagonalOperator (inverseCayleyCoefficientVector Z)

@[simp]
theorem inverseCayleyCoefficientVector_apply (Z : ZeroData)
    (v : ZeroCoordinate Z) :
    inverseCayleyCoefficientVector Z v =
      (cayleyCoefficient (Z.zero v.1))⁻¹ := rfl

@[simp]
theorem zeroCayleyInverseOperator_apply (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) (v : ZeroCoordinate Z) :
    zeroCayleyInverseOperator Z psi v =
      (cayleyCoefficient (Z.zero v.1))⁻¹ * psi v := by
  simp [zeroCayleyInverseOperator]

/-- The reciprocal diagonal operator is a left inverse. -/
theorem zeroCayleyInverseOperator_comp_cayley (Z : ZeroData) :
    zeroCayleyInverseOperator Z * zeroCayleyOperator Z = 1 := by
  apply ContinuousLinearMap.ext
  intro psi
  apply lp.ext
  funext v
  rw [mul_apply_eq_comp, Function.comp_apply,
    zeroCayleyInverseOperator_apply, zeroCayleyOperator_apply]
  rw [← mul_assoc, inv_mul_cancel₀
    (zero_cayley_coefficient_ne_zero Z v.1), one_mul]

/-- The reciprocal diagonal operator is a right inverse. -/
theorem cayley_comp_zeroCayleyInverseOperator (Z : ZeroData) :
    zeroCayleyOperator Z * zeroCayleyInverseOperator Z = 1 := by
  apply ContinuousLinearMap.ext
  intro psi
  apply lp.ext
  funext v
  rw [mul_apply_eq_comp, Function.comp_apply,
    zeroCayleyOperator_apply, zeroCayleyInverseOperator_apply]
  rw [← mul_assoc, mul_inv_cancel₀
    (zero_cayley_coefficient_ne_zero Z v.1), one_mul]

/-- The zero Cayley operator is invertible for every valid `ZeroData`, even
when it is not ordinarily unitary. -/
theorem zeroCayleyOperator_isUnit_unconditional (Z : ZeroData) :
    IsUnit (zeroCayleyOperator Z) := by
  refine ⟨⟨zeroCayleyOperator Z, zeroCayleyInverseOperator Z,
    cayley_comp_zeroCayleyInverseOperator Z,
    zeroCayleyInverseOperator_comp_cayley Z⟩, rfl⟩

/-- The Krein-adjoint inverse candidate `J U* J`. -/
noncomputable def zeroCayleyKreinInverse (Z : ZeroData) :
    MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z :=
  (mirrorFundamentalSymmetry Z :
      MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) *
    star (zeroCayleyOperator Z) *
    (mirrorFundamentalSymmetry Z :
      MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z)

/-- `J U* J` is a left inverse by `U* J U = J` and `J² = I`. -/
theorem zeroCayleyKreinInverse_comp_cayley (Z : ZeroData) :
    zeroCayleyKreinInverse Z * zeroCayleyOperator Z = 1 := by
  let J : MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z :=
    mirrorFundamentalSymmetry Z
  let U : MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z :=
    zeroCayleyOperator Z
  have hJU := congrArg (fun A => J * A)
    (zeroCayleyOperator_j_unitary Z)
  simpa [zeroCayleyKreinInverse, J, U, mul_assoc,
    mirrorFundamentalSymmetry_mul_self] using hJU

/-- The algebraically defined Krein inverse equals the explicit bounded
reciprocal multiplier. -/
theorem zeroCayleyKreinInverse_eq_explicit (Z : ZeroData) :
    zeroCayleyKreinInverse Z = zeroCayleyInverseOperator Z := by
  calc
    zeroCayleyKreinInverse Z = zeroCayleyKreinInverse Z * 1 :=
      (mul_one _).symm
    _ = zeroCayleyKreinInverse Z *
        (zeroCayleyOperator Z * zeroCayleyInverseOperator Z) := by
      rw [cayley_comp_zeroCayleyInverseOperator]
    _ = (zeroCayleyKreinInverse Z * zeroCayleyOperator Z) *
        zeroCayleyInverseOperator Z := by
      rw [mul_assoc]
    _ = zeroCayleyInverseOperator Z := by
      rw [zeroCayleyKreinInverse_comp_cayley, one_mul]

/-- `J U* J` is also a right inverse. -/
theorem cayley_comp_zeroCayleyKreinInverse (Z : ZeroData) :
    zeroCayleyOperator Z * zeroCayleyKreinInverse Z = 1 := by
  rw [zeroCayleyKreinInverse_eq_explicit,
    cayley_comp_zeroCayleyInverseOperator]

/-- The companion Krein conservation identity `U J U* = J`. -/
theorem zeroCayleyOperator_companion_j_unitary (Z : ZeroData) :
    zeroCayleyOperator Z *
        (mirrorFundamentalSymmetry Z :
          MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) *
        star (zeroCayleyOperator Z) =
      (mirrorFundamentalSymmetry Z :
        MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) := by
  let J : MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z :=
    mirrorFundamentalSymmetry Z
  let U : MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z :=
    zeroCayleyOperator Z
  have h := congrArg (fun A => A * J)
    (cayley_comp_zeroCayleyKreinInverse Z)
  simpa [zeroCayleyKreinInverse, J, U, mul_assoc,
    mirrorFundamentalSymmetry_mul_self] using h

/-- Complete Krein inverse package. -/
theorem zero_cayley_krein_inverse_spec (Z : ZeroData) :
    IsUnit (zeroCayleyOperator Z) ∧
      zeroCayleyKreinInverse Z = zeroCayleyInverseOperator Z ∧
      zeroCayleyKreinInverse Z * zeroCayleyOperator Z = 1 ∧
      zeroCayleyOperator Z * zeroCayleyKreinInverse Z = 1 ∧
      zeroCayleyOperator Z *
          (mirrorFundamentalSymmetry Z :
            MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) *
          star (zeroCayleyOperator Z) =
        (mirrorFundamentalSymmetry Z :
          MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) := by
  exact ⟨zeroCayleyOperator_isUnit_unconditional Z,
    zeroCayleyKreinInverse_eq_explicit Z,
    zeroCayleyKreinInverse_comp_cayley Z,
    cayley_comp_zeroCayleyKreinInverse Z,
    zeroCayleyOperator_companion_j_unitary Z⟩

/-- Parameter-free zeta specialization of the Krein inverse formula. -/
theorem zeta_zero_cayley_krein_inverse_spec :
    IsUnit (zeroCayleyOperator zetaZeroData) ∧
      zeroCayleyKreinInverse zetaZeroData *
        zeroCayleyOperator zetaZeroData = 1 ∧
      zeroCayleyOperator zetaZeroData *
        zeroCayleyKreinInverse zetaZeroData = 1 := by
  exact ⟨zeroCayleyOperator_isUnit_unconditional zetaZeroData,
    zeroCayleyKreinInverse_comp_cayley zetaZeroData,
    cayley_comp_zeroCayleyKreinInverse zetaZeroData⟩

#print axioms zeroCayleyOperator_isUnit_unconditional
#print axioms zeroCayleyKreinInverse_eq_explicit
#print axioms zeroCayleyOperator_companion_j_unitary
#print axioms zero_cayley_krein_inverse_spec
#print axioms zeta_zero_cayley_krein_inverse_spec

end D5.S3.Midline.Cayley.CanonicalZetaCayleyKreinInverse
