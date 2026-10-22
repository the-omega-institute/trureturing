/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Transpose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/Transpose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Creation multiplication transposes to the original translated-polynomial coefficient. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Creation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeActualAnnihilation LatticeFiniteNegativeGeneration MvPolynomial
open scoped BigOperators

noncomputable section

def halfTranslationCoeff (D : LatticeData) (charge : Charge D) (degree : ℤ)
    (polynomial : Oscillator D) : Oscillator D :=
  if degree < 0 then 0 else (halfTranslatedPolynomial D charge polynomial).coeff degree.toNat

private theorem half_translation_creator (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (index : Index D) (polynomial : Oscillator D) :
    halfTranslationCoeff D charge degree (X index * polynomial) =
      X index * halfTranslationCoeff D charge degree polynomial -
        (bilinear D charge (unitCharge D index.1) : ℂ) •
          halfTranslationCoeff D charge (degree - (omega D index : ℕ)) polynomial := by
  by_cases negative : degree < 0
  · simp [halfTranslationCoeff, negative,
      show degree - (omega D index : ℕ) < 0 by omega]
  · have shifted : halfTranslationCoeff D charge (degree - (omega D index : ℕ)) polynomial =
        if omega D index ≤ degree.toNat then
          (halfTranslatedPolynomial D charge polynomial).coeff (degree.toNat - omega D index)
        else 0 := by
      by_cases enough : omega D index ≤ degree.toNat
      · simp [halfTranslationCoeff, enough,
          show ¬degree - (omega D index : ℕ) < 0 by omega,
          show (degree - (omega D index : ℕ)).toNat = degree.toNat - omega D index by omega]
      · simp [halfTranslationCoeff, enough,
          show degree - (omega D index : ℕ) < 0 by omega]
    rw [halfTranslationCoeff, if_neg negative, shifted]
    change (halfTranslatedPolynomial D charge (X index * polynomial)).coeff degree.toNat = _
    have product : halfTranslatedPolynomial D charge (X index * polynomial) =
        Polynomial.C (X index) * halfTranslatedPolynomial D charge polynomial -
          Polynomial.C ((bilinear D charge (unitCharge D index.1) : ℂ) •
            (1 : Oscillator D)) *
              (Polynomial.X ^ omega D index * halfTranslatedPolynomial D charge polynomial) := by
      simp only [halfTranslatedPolynomial, map_mul, eval₂AlgHom_X,
        halfTranslationVariable, sub_mul]
      ring
    rw [product]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow_mul', smul_mul_assoc, one_mul,
      halfTranslationCoeff, if_neg negative]

private theorem half_creation_constant (D : LatticeData) (charge : Charge D) (degree : ℤ) :
    constantCoeff (halfCreationCoeff D charge degree) = if degree = 0 then 1 else 0 := by
  by_cases negative : degree < 0
  · simp [halfCreationCoeff, negative, show degree ≠ 0 by omega]
  · by_cases zeroDegree : degree = 0
    · subst degree
      simp [halfCreationCoeff, exponential_constant]
    · rw [if_neg zeroDegree]
      have homogeneous := half_creation_coefficient_grading D charge degree
      apply homogeneous.coeff_eq_zero 0
      simp only [map_zero]
      omega

private theorem oscillator_constant_right (D : LatticeData) (polynomial : Oscillator D)
    (scalar : ℂ) : oscillatorPairing D polynomial (C scalar) =
      scalar * constantCoeff polynomial := by
  have scaling : ∀ polynomial : Oscillator D,
      constantCoeff (scalePolynomial D modeScale polynomial) = constantCoeff polynomial := by
    intro polynomial
    induction polynomial using MvPolynomial.induction_on with
    | C scalar => simp [scalePolynomial_C]
    | add first second firstProof secondProof => simp only [map_add, firstProof, secondProof]
    | mul_X polynomial index previous =>
      simp [map_mul, scalePolynomial_X, map_smul]
  rw [oscillator_pairing_apply]
  change LatticeOscillatorFockForm.gramBilinear D
    (scalePolynomial D modeScale polynomial) (scalePolynomial D modeScale (C scalar)) = _
  rw [scalePolynomial_C, C_eq_smul_one, map_smul]
  have vacuum : LatticeOscillatorFockForm.gramBilinear D
      (scalePolynomial D modeScale polynomial) 1 =
        constantCoeff (scalePolynomial D modeScale polynomial) := by
    run_tac
      let supplier := (Lean.Name.num
        `_private.D5.S3.VertexAlgebra.LatticeOscillatorFockForm 0).append
        `D5.S3.VertexAlgebra.LatticeOscillatorFockForm.gramBilinear_one_right
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _ _))
  rw [vacuum, scaling]
  rfl

private theorem oscillator_creator_right (D : LatticeData) (index : Index D)
    (first second : Oscillator D) :
    oscillatorPairing D first (X index * second) =
      -oscillatorPairing D (LatticeHalfFock.current D index.1 (index.2 : ℤ) first) second := by
  rw [(oscillator_pairing_symm D).eq, oscillator_creator_adjoint,
    (oscillator_pairing_symm D).eq second]

private theorem half_current_product (D : LatticeData) (index : Index D)
    (first second : Oscillator D) :
    LatticeHalfFock.current D index.1 (index.2 : ℤ) (first * second) =
      LatticeHalfFock.current D index.1 (index.2 : ℤ) first * second +
        first * LatticeHalfFock.current D index.1 (index.2 : ℤ) second := by
  change ((index.2 : ℂ) + 1 / 2) • annihilate D index.1 index.2 (first * second) = _
  rw [annihilate_mul]
  simp only [LatticeHalfFock.current, if_neg (show ¬ (index.2 : ℤ) < 0 by omega),
    LatticeHalfFock.frequency, Int.cast_natCast, Int.toNat_natCast,
    LinearMap.smul_apply, smul_add, smul_mul_assoc, mul_smul_comm]

theorem half_creation_multiplication_transpose (D : LatticeData) (charge : Charge D)
    (degree : ℤ) (first second : Oscillator D) :
    oscillatorPairing D (halfCreationCoeff D charge degree * first) second =
      oscillatorPairing D first (halfTranslationCoeff D charge degree second) := by
  classical
  induction second using MvPolynomial.induction_on generalizing first degree with
  | C scalar =>
    have translated : halfTranslationCoeff D charge degree (C scalar) =
        if degree = 0 then C scalar else 0 := by
      by_cases negative : degree < 0
      · simp [halfTranslationCoeff, negative, show degree ≠ 0 by omega]
      · simp [halfTranslationCoeff, negative, halfTranslatedPolynomial,
          Polynomial.coeff_C, show degree.toNat = 0 ↔ degree = 0 by omega]
    rw [oscillator_constant_right, map_mul, half_creation_constant, translated]
    split_ifs <;> simp [oscillator_constant_right]
  | add firstSecond secondSecond firstProof secondProof =>
    have translated : halfTranslationCoeff D charge degree (firstSecond + secondSecond) =
        halfTranslationCoeff D charge degree firstSecond +
          halfTranslationCoeff D charge degree secondSecond := by
      unfold halfTranslationCoeff
      split_ifs <;> simp [halfTranslatedPolynomial]
    simp only [map_add, firstProof, secondProof, translated]
  | mul_X polynomial index previous =>
    rw [mul_comm polynomial (X index), oscillator_creator_right,
      half_current_product, half_current_creation, smul_mul_assoc,
      map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      previous, previous]
    rw [half_translation_creator, map_sub, map_smul,
      oscillator_creator_right, bilinear_symmetric D charge (unitCharge D index.1)]
    simp only [smul_eq_mul]
    ring

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
