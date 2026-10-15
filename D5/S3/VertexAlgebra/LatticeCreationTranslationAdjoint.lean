/- GID: D5/S3/VertexAlgebra/LatticeCreationTranslationAdjoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeCreationTranslationAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native creation and finite polynomial translation coefficient adjoints. -/

import D5.S3.VertexAlgebra.LatticeOscillatorFockForm
import D5.S3.VertexAlgebra.LatticeActualAnnihilation
import D5.S3.VertexAlgebra.LatticeInvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualAnnihilation LatticeActualProductKernel
open LatticeOscillatorFockForm LatticeSugawaraCurrents
open MvPolynomial
open scoped BigOperators

noncomputable section

def translationCoeff (D : LatticeData) (charge : Charge D) (degree : ℤ)
    (polynomial : Oscillator D) : Oscillator D :=
  if degree < 0 then 0 else (translatedPolynomial D charge polynomial).coeff degree.toNat

private theorem creator_right (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    fockForm D (annihilator D coordinate left) right =
      fockForm D left (X coordinate * right) := by
  simpa only [neutralPolynomialMode_positive, neutralPolynomialMode_negative,
    annihilator, LinearMap.smul_apply, LinearMap.mulLeft_apply] using
    fockForm_annihilation_adjoint D 0 coordinate.1 coordinate.2 left right

private theorem annihilator_product (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    annihilator D coordinate (left * right) =
      annihilator D coordinate left * right + left * annihilator D coordinate right := by
  change (coordinate.2 + 1 : ℂ) • annihilate D coordinate.1 coordinate.2 (left * right) =
    ((coordinate.2 + 1 : ℂ) • annihilate D coordinate.1 coordinate.2 left) * right +
      left * ((coordinate.2 + 1 : ℂ) • annihilate D coordinate.1 coordinate.2 right)
  rw [annihilate_mul]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

private theorem annihilator_creation (D : LatticeData) (coordinate : Index D)
    (charge : Charge D) (degree : ℤ) :
    annihilator D coordinate (creationCoeff D charge degree) =
      (bilinear D (unitCharge D coordinate.1) charge : ℂ) •
        creationCoeff D charge (degree - (coordinate.2 + 1 : ℕ)) := by
  change (coordinate.2 + 1 : ℂ) •
    annihilate D coordinate.1 coordinate.2 (creationCoeff D charge degree) = _
  rw [annihilation_creation, smul_smul]
  have frequency_nonzero : (coordinate.2 + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero coordinate.2
  rw [mul_inv_cancel_left₀ frequency_nonzero]

private theorem creation_zero (D : LatticeData) (charge : Charge D) :
    creationCoeff D charge 0 = 1 := by
  classical
  have supplied : VertexOperator.ncoeff (actualField D charge) (-bilinear D charge 0 - 1)
      (Finsupp.single 0 1) = epsilon D charge 0 • Finsupp.single (charge + 0) 1 := by
    apply LatticeFiniteNegativeGeneration.actual_negative_single
    simp [bilinear]
  rw [LatticeActualGeneratorLocality.actual_modes, raw_single_convolution] at supplied
  have convolution_one : convolution D charge 0 (1 : Polynomial (Oscillator D)) =
      creationCoeff D charge 0 := by
    simpa using convolution_monomial D charge 0 0 1
  have coefficient := congrArg (fun state : Carrier D => state charge) supplied
  simpa [bilinear, epsilon, lowerCocycleExponent, paritySign,
    translatedPolynomial, convolution_one] using coefficient

theorem creation_constant (D : LatticeData) (charge : Charge D) (degree : ℤ) :
    constantCoeff (creationCoeff D charge degree) = if degree = 0 then 1 else 0 := by
  by_cases negative : degree < 0
  · simp [creationCoeff, negative, show degree ≠ 0 by omega]
  · by_cases zero_degree : degree = 0
    · subst degree
      simp [creation_zero]
    · rw [if_neg zero_degree]
      have homogeneous := (actual_creation_coefficient_transport D 0 charge).1 degree
      apply homogeneous.coeff_eq_zero 0
      simp only [map_zero]
      omega

private theorem translation_constant (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (scalar : ℂ) :
    translationCoeff D charge degree (C scalar) =
      if degree = 0 then C scalar else 0 := by
  by_cases negative : degree < 0
  · simp [translationCoeff, negative, show degree ≠ 0 by omega]
  · simp [translationCoeff, negative, translatedPolynomial,
      Polynomial.coeff_C, show degree.toNat = 0 ↔ degree = 0 by omega]

theorem translation_polynomial_creator (D : LatticeData) (charge : Charge D)
    (coordinate : Index D) (polynomial : Oscillator D) :
    translatedPolynomial D charge (X coordinate * polynomial) =
      Polynomial.C (X coordinate) * translatedPolynomial D charge polynomial -
        Polynomial.C ((bilinear D charge (unitCharge D coordinate.1) : ℂ) •
          (1 : Oscillator D)) *
            (Polynomial.X ^ (coordinate.2 + 1) * translatedPolynomial D charge polynomial) := by
  simp only [translatedPolynomial, map_mul, eval₂Hom_X', translationVariable, sub_mul]
  ring

private theorem translation_shift_nonnegative (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (coordinate : Index D) (polynomial : Oscillator D) (nonnegative : 0 ≤ degree) :
    translationCoeff D charge (degree - (coordinate.2 + 1 : ℕ)) polynomial =
      if coordinate.2 + 1 ≤ degree.toNat then
        (translatedPolynomial D charge polynomial).coeff (degree.toNat - (coordinate.2 + 1))
      else 0 := by
  by_cases enough : coordinate.2 + 1 ≤ degree.toNat
  · simp only [translationCoeff, if_pos enough,
      if_neg (show ¬degree - (coordinate.2 + 1 : ℕ) < 0 by omega),
      show (degree - (coordinate.2 + 1 : ℕ)).toNat = degree.toNat - (coordinate.2 + 1) by omega]
  · simp only [translationCoeff, if_neg enough,
      if_pos (show degree - (coordinate.2 + 1 : ℕ) < 0 by omega)]

private theorem translation_creator_nonnegative (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (coordinate : Index D) (polynomial : Oscillator D) (nonnegative : 0 ≤ degree) :
    translationCoeff D charge degree (X coordinate * polynomial) =
      X coordinate * translationCoeff D charge degree polynomial -
        (bilinear D charge (unitCharge D coordinate.1) : ℂ) •
          translationCoeff D charge (degree - (coordinate.2 + 1 : ℕ)) polynomial := by
  have shifted := translation_shift_nonnegative D charge degree coordinate polynomial nonnegative
  have unshifted : translationCoeff D charge degree polynomial =
      (translatedPolynomial D charge polynomial).coeff degree.toNat := if_neg (not_lt.mpr nonnegative)
  have left_value : translationCoeff D charge degree (X coordinate * polynomial) =
      (translatedPolynomial D charge (X coordinate * polynomial)).coeff degree.toNat :=
    if_neg (not_lt.mpr nonnegative)
  rw [left_value, translation_polynomial_creator, unshifted, shifted]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul', smul_mul_assoc, one_mul]

private theorem translation_creator (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (coordinate : Index D) (polynomial : Oscillator D) :
    translationCoeff D charge degree (X coordinate * polynomial) =
      X coordinate * translationCoeff D charge degree polynomial -
        (bilinear D charge (unitCharge D coordinate.1) : ℂ) •
          translationCoeff D charge (degree - (coordinate.2 + 1 : ℕ)) polynomial := by
  by_cases negative : degree < 0
  · have zero_left : translationCoeff D charge degree (X coordinate * polynomial) = 0 :=
      if_pos negative
    have zero_unshifted : translationCoeff D charge degree polynomial = 0 := if_pos negative
    have zero_shifted : translationCoeff D charge (degree - (coordinate.2 + 1 : ℕ)) polynomial = 0 :=
      if_pos (by omega)
    rw [zero_left, zero_unshifted, zero_shifted]
    simp
  · exact translation_creator_nonnegative D charge degree coordinate polynomial (by omega)

private theorem vacuum_right (D : LatticeData) (polynomial : Oscillator D) :
    fockForm D polynomial 1 = star (constantCoeff polynomial) := by
  calc
    fockForm D polynomial 1 = star (fockForm D 1 polynomial) :=
      ((fockForm_isSymm D).eq 1 polynomial).symm
    _ = star (constantCoeff polynomial) :=
      congrArg star (fockForm_vacuum_left D polynomial)

private theorem form_constant_right (D : LatticeData) (polynomial : Oscillator D)
    (scalar : ℂ) : fockForm D polynomial (C scalar) = scalar * star (constantCoeff polynomial) := by
  calc
    fockForm D polynomial (C scalar) = fockForm D polynomial (scalar • 1) := by
      rw [C_eq_smul_one]
    _ = scalar * fockForm D polynomial 1 :=
      (fockForm D polynomial).map_smul scalar 1
    _ = scalar * star (constantCoeff polynomial) :=
      congrArg (fun value : ℂ => scalar * value) (vacuum_right D polynomial)

private theorem constant_adjoint (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (left : Oscillator D) (scalar : ℂ) :
    fockForm D (creationCoeff D charge degree * left) (C scalar) =
      fockForm D left (translationCoeff D (-charge) degree (C scalar)) := by
  rw [form_constant_right, map_mul, creation_constant, translation_constant]
  split_ifs
  · simp only [one_mul, form_constant_right]
  · simp only [zero_mul, star_zero, map_zero, mul_zero]

theorem form_integral_smul_left (D : LatticeData) (integer : ℤ)
    (left right : Oscillator D) :
    fockForm D ((integer : ℂ) • left) right = (integer : ℂ) * fockForm D left right := by
  calc
    fockForm D ((integer : ℂ) • left) right =
        star (integer : ℂ) * fockForm D left right :=
      LinearMap.congr_fun ((fockForm D).map_smulₛₗ (integer : ℂ) left) right
    _ = (integer : ℂ) * fockForm D left right :=
      congrArg (fun scalar : ℂ => scalar * fockForm D left right) (star_intCast integer)

theorem creation_translation_adjoint (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (left right : Oscillator D) :
    fockForm D (creationCoeff D charge degree * left) right =
      fockForm D left (translationCoeff D (-charge) degree right) := by
  classical
  induction right using MvPolynomial.induction_on generalizing left degree with
  | C scalar =>
      exact constant_adjoint D charge degree left scalar
  | add first second first_induction second_induction =>
      simp only [map_add, first_induction, second_induction]
      unfold translationCoeff
      split_ifs <;> simp [translatedPolynomial, map_add]
  | mul_X polynomial coordinate induction_hypothesis =>
      rw [mul_comm polynomial (X coordinate), ← creator_right,
        annihilator_product, annihilator_creation]
      rw [smul_mul_assoc, map_add, LinearMap.add_apply, form_integral_smul_left,
        induction_hypothesis, induction_hypothesis, creator_right, translation_creator,
        bilinear_neg_left, Int.cast_neg, neg_smul, sub_neg_eq_add, map_add, map_smul,
        bilinear_symmetric D (unitCharge D coordinate.1) charge]
      exact add_comm _ _

end
end D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint
