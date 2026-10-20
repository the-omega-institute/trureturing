/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native odd-frequency coefficients and the actual ground quotient give coordinate monodromy. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

private theorem ground_neg (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    groundAction D hu (-charge) = groundAction D hu charge := by
  unfold groundAction
  apply congrArg (groundRepresentation D hu)
  apply (quotientEquiv D).injective
  change reduction D (⟨0, -charge⟩ : Extension D) =
    reduction D (⟨0, charge⟩ : Extension D)
  apply SignExtension.ext
  · rfl
  · change reduceCharge D (-charge) = reduceCharge D charge
    funext index
    change ((-charge index : ℤ) : F₂) = (charge index : F₂)
    simp only [Int.cast_neg, CharTwo.neg_eq]

private theorem norm_neg (D : LatticeData) (charge : Charge D) :
    chargeNorm D (-charge) = chargeNorm D charge := by
  simp [chargeNorm, bilinear]

private theorem norm_even (D : LatticeData) (charge : Charge D) :
    Even (chargeNorm D charge) := by
  have symmetrization := integral_cocycle_symmetrization D charge charge
  exact ⟨lowerCocycleExponent D charge charge, symmetrization.symm⟩

private theorem series_neg (D : LatticeData) (charge : Charge D) :
    halfCreationSeries D (-charge) =
      PowerSeries.rescale (-1 : Oscillator D) (halfCreationSeries D charge) := by
  ext degree
  rw [PowerSeries.coeff_rescale]
  by_cases oddDegree : degree % 2 = 1
  · have odd : Odd degree := Nat.odd_iff.mpr oddDegree
    simp [halfCreationSeries, oddDegree, odd.neg_one_pow,
      Finset.sum_neg_distrib, smul_neg]
  · simp [halfCreationSeries, oddDegree]

private theorem exponential_neg (D : LatticeData) (charge : Charge D) :
    halfCreationExponential D (-charge) =
      PowerSeries.rescale (-1 : Oscillator D) (halfCreationExponential D charge) := by
  have zeroConstant : PowerSeries.constantCoeff (halfCreationSeries D charge) = 0 := by
    simp [halfCreationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [halfCreationExponential, series_neg, PowerSeries.rescale_eq_subst,
    halfCreationExponential, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' zeroConstant)
      (PowerSeries.HasSubst.smul_X' (-1 : Oscillator D))]

private theorem creation_neg_nat (D : LatticeData) (charge : Charge D) (degree : ℕ) :
    PowerSeries.coeff degree (halfCreationExponential D (-charge)) =
      ((-1 : ℂ) ^ degree) • PowerSeries.coeff degree (halfCreationExponential D charge) := by
  rw [exponential_neg, PowerSeries.coeff_rescale]
  have coefficientSign : (-1 : Oscillator D) ^ degree =
      MvPolynomial.C ((-1 : ℂ) ^ degree) := by
    simpa only [map_neg, map_one] using
      (map_pow (MvPolynomial.C : ℂ →+* Oscillator D) (-1 : ℂ) degree).symm
  rw [coefficientSign, MvPolynomial.C_mul']

private theorem creation_neg (D : LatticeData) (charge : Charge D) (degree : ℤ) :
    halfCreationCoeff D (-charge) degree =
      ((-1 : ℂ) ^ degree) • halfCreationCoeff D charge degree := by
  by_cases negative : degree < 0
  · simp [halfCreationCoeff, negative]
  · have natural : (degree.toNat : ℤ) = degree := by omega
    have scalarSign : (-1 : ℂ) ^ degree.toNat = (-1 : ℂ) ^ degree := by
      rw [← zpow_natCast, natural]
    calc
      halfCreationCoeff D (-charge) degree =
          PowerSeries.coeff degree.toNat (halfCreationExponential D (-charge)) := by
        rw [halfCreationCoeff, if_neg negative]
      _ = ((-1 : ℂ) ^ degree.toNat) •
          PowerSeries.coeff degree.toNat (halfCreationExponential D charge) :=
        creation_neg_nat D charge degree.toNat
      _ = ((-1 : ℂ) ^ degree) • halfCreationCoeff D charge degree := by
        rw [scalarSign, halfCreationCoeff, if_neg negative]

private theorem polynomial_negative_coefficient {Ring : Type*} [CommRing Ring]
    (polynomial : Polynomial Ring) (degree : ℕ) :
    (Polynomial.eval₂RingHom Polynomial.C (-Polynomial.X) polynomial).coeff degree =
      (-1 : Ring) ^ degree * polynomial.coeff degree := by
  induction polynomial using Polynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [map_add, Polynomial.coeff_add, firstProof, secondProof, mul_add]
  | monomial exponent coefficient =>
    have negativePower : (-Polynomial.X : Polynomial Ring) ^ exponent =
        Polynomial.C ((-1 : Ring) ^ exponent) * Polynomial.X ^ exponent := by
      rw [neg_pow]
      simp only [map_pow, map_neg, map_one]
    change ((Polynomial.monomial exponent coefficient).eval₂ Polynomial.C
      (-Polynomial.X)).coeff degree = _
    rw [Polynomial.eval₂_monomial, negativePower, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.C_mul_X_pow_eq_monomial]
    by_cases same : exponent = degree
    · simp [same, mul_comm]
    · simp [Polynomial.coeff_monomial, same, Ne.symm same]

private theorem translation_neg (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    halfTranslatedPolynomial D (-charge) polynomial =
      Polynomial.eval₂RingHom Polynomial.C (-Polynomial.X)
        (halfTranslatedPolynomial D charge polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [halfTranslatedPolynomial]
  | add first second firstProof secondProof =>
    simp only [halfTranslatedPolynomial, map_add] at firstProof secondProof ⊢
    rw [firstProof, secondProof]
  | mul_X polynomial index inductionProof =>
    have odd : Odd (omega D index) := ⟨index.2, by simp [omega, two_mul]⟩
    simp only [halfTranslatedPolynomial, map_mul, MvPolynomial.eval₂AlgHom_X] at inductionProof ⊢
    rw [inductionProof]
    congr 1
    simp [halfTranslationVariable, bilinear_neg_left, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, odd.neg_pow, neg_smul]

private theorem coefficient_sign (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (degree : ℕ) :
    (-1 : Oscillator D) ^ degree *
      (halfTranslatedPolynomial D charge polynomial).coeff degree =
      ((-1 : ℂ) ^ (degree : ℤ)) •
        (halfTranslatedPolynomial D charge polynomial).coeff degree := by
  rw [zpow_natCast]
  have scalarSign : (-1 : Oscillator D) ^ degree =
        MvPolynomial.C ((-1 : ℂ) ^ degree) := by
    simpa only [map_neg, map_one] using
      (map_pow (MvPolynomial.C : ℂ →+* Oscillator D) (-1 : ℂ) degree).symm
  rw [scalarSign, MvPolynomial.C_mul']

private theorem two_signs (D : LatticeData) (charge : Charge D) (exponent : ℤ)
    (degree : ℕ) : (-1 : ℂ) ^ (degree : ℤ) *
      (-1 : ℂ) ^ (exponent + chargeNorm D charge + degree) = (-1 : ℂ) ^ exponent := by
  have nonzero : (-1 : ℂ) ≠ 0 := by norm_num
  rw [← zpow_add₀ nonzero]
  rw [show (degree : ℤ) + (exponent + chargeNorm D charge + degree) =
    exponent + chargeNorm D charge + 2 * degree by omega]
  rw [zpow_add₀ nonzero, zpow_add₀ nonzero,
    (norm_even D charge).neg_one_zpow, (even_two_mul (degree : ℤ)).neg_one_zpow,
    mul_one, mul_one]

private theorem translated_sign (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (degree : ℕ) :
    (halfTranslatedPolynomial D (-charge) polynomial).coeff degree =
      ((-1 : ℂ) ^ (degree : ℤ)) •
        (halfTranslatedPolynomial D charge polynomial).coeff degree := by
  rw [translation_neg, polynomial_negative_coefficient, coefficient_sign]

private theorem term_scalar_product (D : LatticeData) (first second : ℂ)
    (left right : Oscillator D) :
    (first • left) * (second • right) = (first * second) • (left * right) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

private theorem oscillator_term_neg (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Oscillator D) (degree : ℕ) :
    oscillatorTerm D (-charge) exponent polynomial degree =
      ((-1 : ℂ) ^ exponent) • oscillatorTerm D charge exponent polynomial degree := by
  unfold oscillatorTerm
  rw [norm_neg, translated_sign, creation_neg, term_scalar_product, two_signs]

private theorem oscillator_neg (D : LatticeData) (charge : Charge D) (exponent : ℤ) :
    oscillatorCoefficient D (-charge) exponent =
      ((-1 : ℂ) ^ exponent) • oscillatorCoefficient D charge exponent := by
  apply LinearMap.ext
  intro polynomial
  change (∑ᶠ degree : ℕ, oscillatorTerm D (-charge) exponent polynomial degree) =
    ((-1 : ℂ) ^ exponent) • ∑ᶠ degree : ℕ, oscillatorTerm D charge exponent polynomial degree
  rw [smul_finsum' _ (charged_term_finite_support D charge exponent polynomial)]
  exact finsum_congr (oscillator_term_neg D charge exponent polynomial)

theorem charged_coefficient_coordinate_monodromy (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) :
    chargedCoefficient D hu (-charge) exponent =
      ((-1 : ℂ) ^ exponent) • chargedCoefficient D hu charge exponent := by
  rw [chargedCoefficient, chargedCoefficient, ground_neg, oscillator_neg,
    TensorProduct.map_smul_left]
  have scalar : chargeScalar D (-charge) = chargeScalar D charge := by
    rw [chargeScalar, chargeScalar, norm_neg]
  rw [scalar, smul_smul, smul_smul, mul_comm]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
