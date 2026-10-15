/- GID: D5/S3/VertexAlgebra/LatticeConvolutionFockAdjoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeConvolutionFockAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-integer transpose of the actual finite creation-translation convolution. -/

import D5.S3.VertexAlgebra.LatticeCreationTranslationAdjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeConvolutionFockAdjoint

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualAnnihilation LatticeActualProductKernel
open LatticeOscillatorFockForm LatticeCreationTranslationAdjoint
open MvPolynomial
open scoped BigOperators

noncomputable section

private theorem creator_left (D : LatticeData) (coordinate : Index D)
    (left right : Oscillator D) :
    fockForm D (X coordinate * left) right =
      fockForm D left (annihilator D coordinate right) := by
  apply LatticeOscillatorFockForm.fockForm_creator

private theorem creation_constant (D : LatticeData) (charge : Charge D) (degree : ℤ) :
    constantCoeff (creationCoeff D charge degree) = if degree = 0 then 1 else 0 := by
  apply LatticeCreationTranslationAdjoint.creation_constant

private theorem translation_smul (D : LatticeData) (charge : Charge D)
    (scalar : ℂ) (polynomial : Oscillator D) :
    translatedPolynomial D charge (scalar • polynomial) =
      Polynomial.C (C scalar) * translatedPolynomial D charge polynomial := by
  simp [translatedPolynomial, MvPolynomial.smul_eq_C_mul]

private theorem convolution_creator (D : LatticeData) (charge : Charge D)
    (index : ℤ) (coordinate : Index D) (polynomial : Oscillator D) :
    convolution D charge index (translatedPolynomial D charge (X coordinate * polynomial)) =
      X coordinate * convolution D charge index (translatedPolynomial D charge polynomial) -
        (bilinear D charge (unitCharge D coordinate.1) : ℂ) •
          convolution D charge (index + (coordinate.2 + 1 : ℕ))
            (translatedPolynomial D charge polynomial) := by
  have translation : translatedPolynomial D charge (X coordinate * polynomial) =
      Polynomial.C (X coordinate) * translatedPolynomial D charge polynomial -
        Polynomial.C ((bilinear D charge (unitCharge D coordinate.1) : ℂ) •
          (1 : Oscillator D)) *
          (Polynomial.X ^ (coordinate.2 + 1) * translatedPolynomial D charge polynomial) := by
    apply LatticeCreationTranslationAdjoint.translation_polynomial_creator
  rw [translation, map_sub, convolution_C_mul, convolution_C_mul, convolution_X_pow]
  simp only [smul_mul_assoc, one_mul]

private theorem convolution_annihilator (D : LatticeData) (charge : Charge D)
    (index : ℤ) (coordinate : Index D) (polynomial : Oscillator D) :
    annihilator D coordinate
      (convolution D charge index (translatedPolynomial D charge polynomial)) =
      convolution D charge index (translatedPolynomial D charge (annihilator D coordinate polynomial)) +
        (bilinear D (unitCharge D coordinate.1) charge : ℂ) •
          convolution D charge (index - (coordinate.2 + 1 : ℕ))
            (translatedPolynomial D charge polynomial) := by
  have frequency_nonzero : (coordinate.2 + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero coordinate.2
  change (coordinate.2 + 1 : ℂ) • annihilate D coordinate.1 coordinate.2
      (convolution D charge index (translatedPolynomial D charge polynomial)) =
    convolution D charge index (translatedPolynomial D charge
      ((coordinate.2 + 1 : ℂ) • annihilate D coordinate.1 coordinate.2 polynomial)) + _
  rw [annihilation_convolution, ← annihilation_transport, smul_add,
    translation_smul, convolution_C_mul]
  simp only [← MvPolynomial.smul_eq_C_mul, smul_smul,
    mul_inv_cancel_left₀ frequency_nonzero]

private theorem convolution_constant (D : LatticeData) (charge : Charge D)
    (index : ℤ) (polynomial : Polynomial (Oscillator D)) :
    constantCoeff (convolution D charge index polynomial) =
      if index ≤ 0 then constantCoeff (polynomial.coeff (-index).toNat) else 0 := by
  classical
  induction polynomial using Polynomial.induction_on' with
  | add first second first_induction second_induction =>
      simp only [map_add, first_induction, second_induction, Polynomial.coeff_add]
      split_ifs <;> ring
  | monomial degree coefficient =>
      rw [convolution_monomial, map_mul, creation_constant]
      by_cases nonpositive : index ≤ 0
      · have matching : index + (degree : ℤ) = 0 ↔ degree = (-index).toNat := by omega
        by_cases degree_eq : degree = (-index).toNat
        · simp [nonpositive, Polynomial.coeff_monomial, matching, degree_eq]
        · simp [nonpositive, Polynomial.coeff_monomial, matching, degree_eq, Ne.symm degree_eq]
      · simp [nonpositive, show index + (degree : ℤ) ≠ 0 by omega]

private theorem translated_convolution_constant (D : LatticeData) (charge : Charge D)
    (index : ℤ) (polynomial : Oscillator D) :
    constantCoeff (convolution D charge (-index) (translatedPolynomial D charge polynomial)) =
      constantCoeff (translationCoeff D charge index polynomial) := by
  rw [convolution_constant]
  by_cases negative : index < 0
  · simp [translationCoeff, negative, show ¬-index ≤ 0 by omega]
  · simp [translationCoeff, negative, show -index ≤ 0 by omega]

private theorem convolution_scalar (D : LatticeData) (charge : Charge D)
    (index : ℤ) (scalar : ℂ) :
    convolution D charge index (translatedPolynomial D charge (C scalar)) =
      scalar • creationCoeff D charge index := by
  have translated : translatedPolynomial D charge (C scalar) = Polynomial.C (C scalar) := by
    simp [translatedPolynomial]
  rw [translated]
  change convolution D charge index (Polynomial.monomial 0 (C scalar)) = _
  rw [convolution_monomial]
  simp only [Nat.cast_zero, add_zero, MvPolynomial.smul_eq_C_mul]

private theorem convolution_vacuum_adjoint (D : LatticeData) (charge : Charge D)
    (index : ℤ) (scalar : ℂ) (right : Oscillator D) :
    fockForm D (convolution D charge index (translatedPolynomial D charge (C scalar))) right =
      fockForm D (C scalar)
        (convolution D (-charge) (-index) (translatedPolynomial D (-charge) right)) := by
  rw [convolution_scalar, C_eq_smul_one]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
  congr 1
  have adjoint := creation_translation_adjoint D charge index 1 right
  simpa only [mul_one, fockForm_vacuum_left, translated_convolution_constant] using adjoint

private theorem form_integral_smul_left (D : LatticeData) (integer : ℤ)
    (left right : Oscillator D) :
    fockForm D ((integer : ℂ) • left) right = (integer : ℂ) * fockForm D left right := by
  apply LatticeCreationTranslationAdjoint.form_integral_smul_left

theorem convolution_transpose (D : LatticeData) (charge : Charge D) (index : ℤ)
    (left right : Oscillator D) :
    fockForm D (convolution D charge index (translatedPolynomial D charge left)) right =
      fockForm D left
        (convolution D (-charge) (-index) (translatedPolynomial D (-charge) right)) := by
  classical
  induction left using MvPolynomial.induction_on generalizing index right with
  | C scalar =>
      exact convolution_vacuum_adjoint D charge index scalar right
  | add first second first_induction second_induction =>
      have translated_add : translatedPolynomial D charge (first + second) =
          translatedPolynomial D charge first + translatedPolynomial D charge second :=
        map_add _ _ _
      simp only [translated_add, map_add, LinearMap.add_apply,
        first_induction, second_induction]
  | mul_X polynomial coordinate induction_hypothesis =>
      rw [mul_comm polynomial (X coordinate), convolution_creator]
      rw [map_sub, LinearMap.sub_apply, form_integral_smul_left]
      rw [creator_left, induction_hypothesis, induction_hypothesis, creator_left,
        convolution_annihilator]
      have reflected : -index - (coordinate.2 + 1 : ℕ) =
          -(index + (coordinate.2 + 1 : ℕ)) := by omega
      simp only [map_add, map_smul, bilinear_neg_right, Int.cast_neg,
        bilinear_symmetric, neg_smul, map_neg, reflected, smul_eq_mul]
      ring

end
end D5.S3.VertexAlgebra.LatticeConvolutionFockAdjoint
