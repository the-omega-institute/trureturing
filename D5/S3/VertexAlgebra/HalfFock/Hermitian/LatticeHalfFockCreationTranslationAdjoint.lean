/- GID: D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockCreationTranslationAdjoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockCreationTranslationAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native half-frequency creation and finite translation coefficient transpose. -/

import D5.S3.VertexAlgebra.HalfFock.Hermitian.LatticeHalfFockHermitian
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCreationTranslationAdjoint

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFock LatticeHalfFockHermitian LatticeHalfFockChargedCoefficients
open LatticeOscillatorFockForm MvPolynomial
open scoped BigOperators

noncomputable section

def halfTranslationCoeff (D : LatticeData) (charge : Charge D) (degree : ℤ)
    (polynomial : Oscillator D) : Oscillator D :=
  if degree < 0 then 0 else (halfTranslatedPolynomial D charge polynomial).coeff degree.toNat

private theorem creator_right (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    halfForm D (current D coordinate.1 coordinate.2 left) right =
      halfForm D left (X coordinate * right) := by
  simpa only [current_negative, LinearMap.mulLeft_apply] using
    halfForm_current_adjoint D coordinate.1 coordinate.2 left right

private theorem current_product (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    current D coordinate.1 coordinate.2 (left * right) =
      current D coordinate.1 coordinate.2 left * right +
        left * current D coordinate.1 coordinate.2 right := by
  simp only [current, show ¬(coordinate.2 : ℤ) < 0 by omega, if_false,
    Int.toNat_natCast, LinearMap.smul_apply, LatticeActualAnnihilation.annihilate_mul,
    smul_add, smul_mul_assoc, mul_smul_comm]

private theorem current_creation (D : LatticeData) (coordinate : Index D)
    (charge : Charge D) (degree : ℤ) :
    current D coordinate.1 coordinate.2 (halfCreationCoeff D charge degree) =
      (bilinear D (unitCharge D coordinate.1) charge : ℂ) •
        halfCreationCoeff D charge (degree - (omega D coordinate : ℕ)) := by
  simp only [current, show ¬(coordinate.2 : ℤ) < 0 by omega, if_false,
    Int.toNat_natCast, LinearMap.smul_apply, half_annihilation_creation, smul_smul]
  have balance : frequency coordinate.2 * (2 / (2 * coordinate.2 + 1 : ℂ)) = 1 := by
    have nonzero : (2 * (coordinate.2 : ℂ) + 1) ≠ 0 := by
      exact_mod_cast (show 2 * coordinate.2 + 1 ≠ 0 by omega)
    change ((coordinate.2 : ℂ) + 1 / 2) * (2 / (2 * (coordinate.2 : ℂ) + 1)) = 1
    simp only [div_eq_mul_inv]
    rw [← mul_assoc,
      show ((coordinate.2 : ℂ) + 1 * (2 : ℂ)⁻¹) * 2 =
        2 * (coordinate.2 : ℂ) + 1 by ring,
      mul_inv_cancel₀ nonzero]
  rw [← mul_assoc, balance, one_mul]
  rfl

theorem creation_constant (D : LatticeData) (charge : Charge D) (degree : ℤ) :
    constantCoeff (halfCreationCoeff D charge degree) = if degree = 0 then 1 else 0 := by
  by_cases negative : degree < 0
  · simp [halfCreationCoeff, negative, show degree ≠ 0 by omega]
  · by_cases zero_degree : degree = 0
    · subst degree
      simp [halfCreationCoeff, exponential_constant]
    · rw [if_neg zero_degree]
      have homogeneous := half_creation_coefficient_grading D charge degree
      apply homogeneous.coeff_eq_zero 0
      simp only [map_zero]
      omega

private theorem translation_constant (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (scalar : ℂ) :
    halfTranslationCoeff D charge degree (C scalar) =
      if degree = 0 then C scalar else 0 := by
  by_cases negative : degree < 0
  · simp [halfTranslationCoeff, negative, show degree ≠ 0 by omega]
  · simp [halfTranslationCoeff, negative, halfTranslatedPolynomial,
      Polynomial.coeff_C, show degree.toNat = 0 ↔ degree = 0 by omega]

private theorem translation_polynomial_creator (D : LatticeData) (charge : Charge D)
    (coordinate : Index D) (polynomial : Oscillator D) :
    halfTranslatedPolynomial D charge (X coordinate * polynomial) =
      Polynomial.C (X coordinate) * halfTranslatedPolynomial D charge polynomial -
        Polynomial.C ((bilinear D charge (unitCharge D coordinate.1) : ℂ) •
          (1 : Oscillator D)) *
            (Polynomial.X ^ omega D coordinate * halfTranslatedPolynomial D charge polynomial) := by
  simp only [halfTranslatedPolynomial, map_mul, eval₂AlgHom_X, halfTranslationVariable, sub_mul]
  ring

private theorem translation_creator (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (coordinate : Index D) (polynomial : Oscillator D) :
    halfTranslationCoeff D charge degree (X coordinate * polynomial) =
      X coordinate * halfTranslationCoeff D charge degree polynomial -
        (bilinear D charge (unitCharge D coordinate.1) : ℂ) •
          halfTranslationCoeff D charge (degree - (omega D coordinate : ℕ)) polynomial := by
  by_cases negative : degree < 0
  · simp [halfTranslationCoeff, negative,
      show degree - (omega D coordinate : ℕ) < 0 by simp only [omega]; omega]
  · have shifted : halfTranslationCoeff D charge (degree - (omega D coordinate : ℕ)) polynomial =
        if omega D coordinate ≤ degree.toNat then
          (halfTranslatedPolynomial D charge polynomial).coeff (degree.toNat - omega D coordinate)
        else 0 := by
      by_cases enough : omega D coordinate ≤ degree.toNat
      · simp only [halfTranslationCoeff, if_pos enough,
          if_neg (show ¬degree - (omega D coordinate : ℕ) < 0 by omega),
          show (degree - (omega D coordinate : ℕ)).toNat = degree.toNat - omega D coordinate by omega]
      · simp only [halfTranslationCoeff, if_neg enough,
          if_pos (show degree - (omega D coordinate : ℕ) < 0 by omega)]
    rw [halfTranslationCoeff, if_neg negative, translation_polynomial_creator]
    rw [show halfTranslationCoeff D charge degree polynomial =
      (halfTranslatedPolynomial D charge polynomial).coeff degree.toNat from if_neg negative, shifted]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow_mul', smul_mul_assoc, one_mul]

private theorem constant_scaling (D : LatticeData) (polynomial : Oscillator D) :
    constantCoeff (scaling D polynomial) = constantCoeff polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [scaling]
  | add first second firstProof secondProof => simp [map_add, firstProof, secondProof]
  | mul_X polynomial coordinate previous => simp [scaling, map_mul]

theorem vacuum_left (D : LatticeData) (polynomial : Oscillator D) :
    halfForm D 1 polynomial = constantCoeff polynomial := by
  rw [halfForm_apply, map_one, fockForm_vacuum_left, constant_scaling]

private theorem vacuum_right (D : LatticeData) (polynomial : Oscillator D) :
    halfForm D polynomial 1 = star (constantCoeff polynomial) := by
  rw [← (halfForm_isSymm D).eq 1 polynomial, vacuum_left]
  rfl

private theorem form_constant_right (D : LatticeData) (polynomial : Oscillator D)
    (scalar : ℂ) : halfForm D polynomial (C scalar) = scalar * star (constantCoeff polynomial) := by
  rw [C_eq_smul_one, map_smul, smul_eq_mul, vacuum_right]

private theorem constant_adjoint (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (left : Oscillator D) (scalar : ℂ) :
    halfForm D (halfCreationCoeff D charge degree * left) (C scalar) =
      halfForm D left (halfTranslationCoeff D (-charge) degree (C scalar)) := by
  rw [form_constant_right, map_mul, creation_constant, translation_constant]
  split_ifs
  · simp only [one_mul, form_constant_right]
  · simp only [zero_mul, star_zero, map_zero, mul_zero]

theorem form_integral_smul_left (D : LatticeData) (integer : ℤ)
    (left right : Oscillator D) :
    halfForm D ((integer : ℂ) • left) right = (integer : ℂ) * halfForm D left right := by
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_intCast, smul_eq_mul]

theorem half_creation_translation_adjoint (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (left right : Oscillator D) :
    halfForm D (halfCreationCoeff D charge degree * left) right =
      halfForm D left (halfTranslationCoeff D (-charge) degree right) := by
  classical
  induction right using MvPolynomial.induction_on generalizing left degree with
  | C scalar => exact constant_adjoint D charge degree left scalar
  | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof]
      unfold halfTranslationCoeff
      split_ifs <;> simp [halfTranslatedPolynomial, map_add]
  | mul_X polynomial coordinate previous =>
      rw [mul_comm polynomial (X coordinate), ← creator_right,
        current_product, current_creation]
      rw [smul_mul_assoc, map_add, LinearMap.add_apply, form_integral_smul_left,
        previous, previous, creator_right, translation_creator,
        bilinear_neg_left, Int.cast_neg, neg_smul, sub_neg_eq_add, map_add, map_smul,
        bilinear_symmetric D (unitCharge D coordinate.1) charge]
      exact add_comm _ _

end
end D5.S3.VertexAlgebra.LatticeHalfFockCreationTranslationAdjoint
