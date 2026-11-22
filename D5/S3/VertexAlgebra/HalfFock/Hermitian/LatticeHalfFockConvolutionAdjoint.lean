/- GID: D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockConvolutionAdjoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockConvolutionAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-charge native oscillator coefficient transpose with exact reflected exponent. -/

import D5.S3.VertexAlgebra.HalfFock.Hermitian.LatticeHalfFockCreationTranslationAdjoint
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockConvolutionAdjoint

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFock LatticeHalfFockHermitian LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCreationTranslationAdjoint
open MvPolynomial
open scoped BigOperators

noncomputable section

private theorem creator_left (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    halfForm D (X coordinate * left) right =
      halfForm D left (current D coordinate.1 coordinate.2 right) := by
  simpa only [current_negative, LinearMap.mulLeft_apply] using
    halfForm_creation_adjoint D coordinate.1 coordinate.2 left right

private theorem coefficient_sum (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Oscillator D) :
    oscillatorCoefficient D charge exponent polynomial =
      ∑ degree ∈ (halfTranslatedPolynomial D charge polynomial).support,
        (halfTranslatedPolynomial D charge polynomial).coeff degree *
          halfCreationCoeff D charge (exponent + chargeNorm D charge + degree) := by
  change (∑ᶠ degree : ℕ, oscillatorTerm D charge exponent polynomial degree) = _
  rw [finsum_eq_sum_of_support_subset _ (term_support D charge exponent polynomial)]
  rfl

private theorem coefficient_current (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (coordinate : Index D) (polynomial : Oscillator D) :
    current D coordinate.1 coordinate.2 (oscillatorCoefficient D charge exponent polynomial) =
      oscillatorCoefficient D charge exponent (current D coordinate.1 coordinate.2 polynomial) +
        (bilinear D (unitCharge D coordinate.1) charge : ℂ) •
          oscillatorCoefficient D charge (exponent - omega D coordinate) polynomial := by
  have ward := oscillator_current_ward D coordinate.1 charge coordinate.2 exponent polynomial
  have reflected : (omega D coordinate : ℤ) = 2 * (coordinate.2 : ℤ) + 1 := by
    simp [omega]
  rw [reflected]
  exact (sub_eq_iff_eq_add.mp ward).trans (add_comm _ _)

private theorem coefficient_constant (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Oscillator D) :
    constantCoeff (oscillatorCoefficient D charge exponent polynomial) =
      if exponent + chargeNorm D charge ≤ 0 then
        constantCoeff ((halfTranslatedPolynomial D charge polynomial).coeff
          (-exponent - chargeNorm D charge).toNat)
      else 0 := by
  classical
  rw [coefficient_sum, map_sum]
  simp only [map_mul, creation_constant]
  by_cases nonpositive : exponent + chargeNorm D charge ≤ 0
  · rw [if_pos nonpositive]
    rw [Finset.sum_eq_single (-exponent - chargeNorm D charge).toNat]
    · rw [if_pos (by omega), mul_one]
    · intro degree hdegree different
      rw [if_neg (by omega), mul_zero]
    · intro absent
      have zero : (halfTranslatedPolynomial D charge polynomial).coeff
          (-exponent - chargeNorm D charge).toNat = 0 := by
        by_contra nonzero
        exact absent (Polynomial.mem_support_iff.mpr nonzero)
      simp [zero]
  · rw [if_neg nonpositive]
    apply Finset.sum_eq_zero
    intro degree hdegree
    rw [if_neg (by omega), mul_zero]

private theorem norm_negative (D : LatticeData) (charge : Charge D) :
    chargeNorm D (-charge) = chargeNorm D charge := by
  simp [chargeNorm, bilinear_neg_left, bilinear_neg_right]

private theorem reflected_constant (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (polynomial : Oscillator D) :
    constantCoeff (oscillatorCoefficient D (-charge)
      (-exponent - 2 * chargeNorm D charge) polynomial) =
        constantCoeff (halfTranslationCoeff D (-charge) (exponent + chargeNorm D charge) polynomial) := by
  rw [coefficient_constant, norm_negative]
  by_cases negative : exponent + chargeNorm D charge < 0
  · simp [halfTranslationCoeff, negative,
      show ¬-exponent - 2 * chargeNorm D charge + chargeNorm D charge ≤ 0 by omega]
  · simp only [halfTranslationCoeff, if_neg negative,
      if_pos (show -exponent - 2 * chargeNorm D charge + chargeNorm D charge ≤ 0 by omega),
      show -(-exponent - 2 * chargeNorm D charge) - chargeNorm D charge =
        exponent + chargeNorm D charge by ring]

private theorem coefficient_scalar (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (scalar : ℂ) :
    oscillatorCoefficient D charge exponent (C scalar) =
      scalar • halfCreationCoeff D charge (exponent + chargeNorm D charge) := by
  have supplied : oscillatorCoefficient D charge exponent (1 : Oscillator D) =
      halfCreationCoeff D charge (exponent + chargeNorm D charge) := by
    have oneTranslation : halfTranslatedPolynomial D charge (1 : Oscillator D) = 1 :=
      map_one (MvPolynomial.eval₂AlgHom ℂ (halfTranslationVariable D charge))
    have supportOne : (1 : Polynomial (Oscillator D)).support = {0} := by
      rw [← Polynomial.C_1, Polynomial.support_C (one_ne_zero : (1 : Oscillator D) ≠ 0)]
    rw [coefficient_sum, oneTranslation, supportOne]
    simp [Polynomial.coeff_one]
  rw [C_eq_smul_one, map_smul, supplied]

private theorem coefficient_vacuum_adjoint (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (scalar : ℂ) (right : Oscillator D) :
    halfForm D (oscillatorCoefficient D charge exponent (C scalar)) right =
      halfForm D (C scalar)
        (oscillatorCoefficient D (-charge) (-exponent - 2 * chargeNorm D charge) right) := by
  rw [coefficient_scalar, C_eq_smul_one]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
  congr 1
  have adjoint := half_creation_translation_adjoint D charge
    (exponent + chargeNorm D charge) 1 right
  simpa only [mul_one, vacuum_left, reflected_constant] using adjoint

theorem oscillator_coefficient_adjoint (D : LatticeData) (charge : Charge D)
    (exponent : ℤ) (left right : Oscillator D) :
    halfForm D (oscillatorCoefficient D charge exponent left) right =
      halfForm D left
        (oscillatorCoefficient D (-charge) (-exponent - 2 * chargeNorm D charge) right) := by
  classical
  induction left using MvPolynomial.induction_on generalizing exponent right with
  | C scalar => exact coefficient_vacuum_adjoint D charge exponent scalar right
  | add first second firstProof secondProof =>
      simp only [map_add, LinearMap.add_apply, firstProof, secondProof]
  | mul_X polynomial coordinate previous =>
      rw [mul_comm polynomial (X coordinate), oscillator_coefficient_X_mul]
      rw [map_sub, LinearMap.sub_apply, form_integral_smul_left]
      rw [creator_left, previous, previous, creator_left, coefficient_current]
      have reflected : -exponent - 2 * chargeNorm D charge - (omega D coordinate : ℕ) =
          -(exponent + (omega D coordinate : ℕ)) - 2 * chargeNorm D charge := by omega
      simp only [map_add, map_smul, bilinear_neg_right, Int.cast_neg,
        bilinear_symmetric, neg_smul, map_neg, reflected, smul_eq_mul]
      ring

end
end D5.S3.VertexAlgebra.LatticeHalfFockConvolutionAdjoint
