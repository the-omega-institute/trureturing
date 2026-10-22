/- GID: D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical derivative covariance for original charged corrected source states. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedTranslationExtension
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFirstDescendant LatticeHalfFockTranslationCalculus
open LatticeHalfFockAllStateField LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectionTranslation LatticeHalfFockChargedTranslationExtension
open MvPolynomial
open scoped BigOperators

noncomputable section

private def physicalDerivativeLinear (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (NativeField D hu) where
  toFun := physicalDerivative D hu
  map_add' first second := by
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    simp only [physicalDerivative, HVertexOperator.coeff_of_coeff, map_add, Pi.add_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_add]
  map_smul' scalar field := by
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    simp only [physicalDerivative, HVertexOperator.coeff_of_coeff, map_smul,
      Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [smul_comm]

private theorem shift_add (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : ℕ) (field : NativeField D hu) :
    shiftLinear D hu first (shiftLinear D hu second field) =
      shiftLinear D hu (first + second) field := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  simp only [shiftLinear, shiftField, HVertexOperator.coeff_of_coeff,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [show exponent + 2 * first + 2 * second =
      exponent + 2 * ((first + second : ℕ) : ℤ) by omega]

private theorem shift_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) :
    physicalDerivative D hu (shiftLinear D hu 1 field) =
      shiftLinear D hu 1 (physicalDerivative D hu field) - shiftLinear D hu 2 field := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  change (((exponent + 2 : ℤ) : ℂ) / 2) • field.coeff (exponent + 2 + 2) vector =
    (((exponent + 2 + 2 : ℤ) : ℂ) / 2) • field.coeff (exponent + 2 + 2) vector -
      field.coeff (exponent + 4) vector
  rw [show exponent + 2 + 2 = exponent + 4 by omega]
  push_cast
  module

private theorem shift_insertion (D : LatticeData) (hu : IsUnit D.G.det)
    (shift : ℕ) (index : Index D) (field : NativeField D hu) :
    shiftLinear D hu shift (normalInsertion D hu index field) =
      normalInsertion D hu index (shiftLinear D hu shift field) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  simp only [shiftLinear, shiftField, normalInsertion, normalCoefficient,
    HVertexOperator.coeff_of_coeff, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  · apply finsum_congr
    intro offset
    change jetScalar index.2 (-(offset : ℤ) - 1) •
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 (-(offset : ℤ) - 1)
        (field.coeff (exponent + 2 * shift - 2 * offset + 2 * index.2 + 1) vector) =
      jetScalar index.2 (-(offset : ℤ) - 1) •
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 (-(offset : ℤ) - 1)
          (field.coeff (exponent - 2 * offset + 2 * index.2 + 1 + 2 * shift) vector)
    rw [show exponent + 2 * shift - 2 * offset + 2 * index.2 + 1 =
        exponent - 2 * offset + 2 * index.2 + 1 + 2 * shift by omega]
  · apply finsum_congr
    intro offset
    change jetScalar index.2 offset •
      field.coeff (exponent + 2 * shift + 2 * offset + 2 * index.2 + 3)
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 offset vector) =
      jetScalar index.2 offset • field.coeff (exponent + 2 * offset + 2 * index.2 + 3 + 2 * shift)
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) index.1 offset vector)
    rw [show exponent + 2 * shift + 2 * offset + 2 * index.2 + 3 =
        exponent + 2 * offset + 2 * index.2 + 3 + 2 * shift by omega]

private theorem normalPolynomial_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (polynomial : Oscillator D) :
    normalPolynomial D hu charge (X index * polynomial) =
      normalInsertionLinear D hu index (normalPolynomial D hu charge polynomial) := by
  classical
  have enumeration (exponent : Index D →₀ ℕ) :
      (index :: LatticeAllStateField.occurrences D exponent).Perm
        (LatticeAllStateField.occurrences D (Finsupp.single index 1 + exponent)) := by
    apply Multiset.coe_eq_coe.mp
    simp [LatticeAllStateField.occurrences, Finsupp.toMultiset_add]
    change index ::ₘ ((Finsupp.toMultiset exponent).toList : Multiset (Index D)) = _
    rw [Multiset.coe_toList]
  rw [polynomial.as_sum, Finset.mul_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro exponent member
  have monomial : MvPolynomial.monomial exponent (coeff exponent polynomial) =
      coeff exponent polynomial • MvPolynomial.monomial exponent 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [monomial]
  simp only [mul_smul_comm, map_smul, RingHom.id_apply]
  congr 1
  rw [show (X index : Oscillator D) * MvPolynomial.monomial exponent (1 : ℂ) =
      MvPolynomial.monomial (Finsupp.single index 1 + exponent) (1 : ℂ) by
        simp only [X, monomial_mul, one_mul],
    normalPolynomial_monomial_enumeration D hu charge _ _ (enumeration exponent),
    normalWord, normalPolynomial_monomial_enumeration D hu charge exponent _ (List.Perm.refl _)]
  rfl

private def polynomialEvaluation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) : Polynomial (Oscillator D) →ₗ[ℂ] NativeField D hu :=
  (Finsupp.lsum ℂ (fun shift : ℕ =>
    (shiftLinear D hu shift).comp (normalPolynomial D hu charge))).comp (shiftCoefficients D)

private theorem polynomialEvaluation_monomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (shift : ℕ) (polynomial : Oscillator D) :
    polynomialEvaluation D hu charge (Polynomial.monomial shift polynomial) =
      shiftLinear D hu shift (normalPolynomial D hu charge polynomial) := by
  have coefficient : shiftCoefficients D (Polynomial.monomial shift polynomial) =
      Finsupp.single shift polynomial := by
    ext degree
    simp [shiftCoefficients, Polynomial.coeff_monomial]
  simp only [polynomialEvaluation, LinearMap.comp_apply, coefficient, Finsupp.lsum_single]

private theorem polynomialEvaluation_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Polynomial (Oscillator D)) :
    polynomialEvaluation D hu charge (Polynomial.X * polynomial) =
      shiftLinear D hu 1 (polynomialEvaluation D hu charge polynomial) := by
  induction polynomial using Polynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [mul_add, map_add, firstProof, secondProof]
  | monomial shift polynomial =>
    rw [Polynomial.X_mul_monomial, polynomialEvaluation_monomial,
      polynomialEvaluation_monomial, shift_add]
    rw [Nat.add_comm]

private theorem polynomialEvaluation_C_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (polynomial : Polynomial (Oscillator D)) :
    polynomialEvaluation D hu charge (Polynomial.C (X index) * polynomial) =
      normalInsertionLinear D hu index (polynomialEvaluation D hu charge polynomial) := by
  induction polynomial using Polynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [mul_add, map_add, firstProof, secondProof]
  | monomial shift polynomial =>
    rw [Polynomial.C_mul_monomial, polynomialEvaluation_monomial,
      polynomialEvaluation_monomial, normalPolynomial_X_mul]
    exact shift_insertion D hu shift index _

private def normalEvaluation (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    CorrectionPolynomial D →ₗ[ℂ] NativeField D hu :=
  (polynomialEvaluation D hu charge).comp (optionEquivLeft ℂ (Index D)).toLinearMap

private theorem normalEvaluation_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (polynomial : CorrectionPolynomial D) :
    normalEvaluation D hu charge (X (some index) * polynomial) =
      normalInsertionLinear D hu index (normalEvaluation D hu charge polynomial) := by
  simp only [normalEvaluation, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul, optionEquivLeft_X_some]
  exact polynomialEvaluation_C_X_mul D hu charge index _

private theorem normalEvaluation_shift_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : CorrectionPolynomial D) :
    normalEvaluation D hu charge (X none * polynomial) =
      shiftLinear D hu 1 (normalEvaluation D hu charge polynomial) := by
  simp only [normalEvaluation, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul, optionEquivLeft_X_none]
  exact polynomialEvaluation_X_mul D hu charge _

private def oscillatorConnection (D : LatticeData) :
    Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D) :=
  mkDerivation ℂ fun coordinate => match coordinate with
    | none => -(X none ^ 2)
    | some index => (sourceWeight D index : ℂ) • X (some (successorIndex D index))

private def chargeMultiplier (D : LatticeData) (charge : Charge D) : CorrectionPolynomial D :=
  (∑ colour : Fin D.rank, (charge colour : ℂ) • X (some (colour, 0))) -
    ((chargeNorm D charge : ℂ) / 2) • X none

private def correctionPhysicalOperation (D : LatticeData) (charge : Charge D) :
    Module.End ℂ (CorrectionPolynomial D) :=
  (oscillatorConnection D).toLinearMap + LinearMap.mulLeft ℂ (chargeMultiplier D charge)

private theorem pairing_self (D : LatticeData) (charge : Charge D) :
    (∑ colour : Fin D.rank, (charge colour : ℂ) *
      (bilinear D (unitCharge D colour) charge : ℂ)) = (chargeNorm D charge : ℂ) := by
  simp [chargeNorm, bilinear, unitCharge, Int.cast_sum, Finset.mul_sum, mul_assoc]

private theorem singleton_sum (D : LatticeData) (charge : Charge D) :
    (∑ colour : Fin D.rank, (charge colour : ℂ) • singletonPolynomial D charge (colour, 0)) =
      -((chargeNorm D charge : ℂ) / 2) • X none := by
  have first : halfBinomial 1 = -1 / 2 := by norm_num [halfBinomial]
  simp only [singletonPolynomial, sourceWeight, Nat.zero_add, first, pow_one,
    ← MvPolynomial.smul_eq_C_mul, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  calc
    (∑ colour, (charge colour : ℂ) *
      ((-1 / 2) * (bilinear D (unitCharge D colour) charge : ℂ))) =
        (-1 / 2 : ℂ) * ∑ colour, (charge colour : ℂ) *
          (bilinear D (unitCharge D colour) charge : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro colour member
            ring
    _ = -((chargeNorm D charge : ℂ) / 2) := by rw [pairing_self]; ring

private theorem correction_operation_identity (D : LatticeData) (charge : Charge D)
    (polynomial : CorrectionPolynomial D) :
    correctionConnection D charge polynomial +
      ∑ colour : Fin D.rank, (charge colour : ℂ) • insertion D charge (colour, 0) polynomial =
        correctionPhysicalOperation D charge polynomial := by
  have sum_apply (family : Fin D.rank → Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D))
      (argument : CorrectionPolynomial D) :
      (∑ colour, family colour) argument = ∑ colour, family colour argument := by
    have mapped := map_sum (Derivation.coeFnAddMonoidHom (R := ℂ) (A := CorrectionPolynomial D)
      (M := CorrectionPolynomial D)) family Finset.univ
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
      congrArg (fun function => function argument) mapped
  have compensated : correctionConnection D charge +
      ∑ colour : Fin D.rank, (charge colour : ℂ) • pairDerivation D (colour, 0) =
        oscillatorConnection D := by
    apply MvPolynomial.derivation_ext
    intro coordinate
    cases coordinate with
    | none =>
      simp [Derivation.add_apply, sum_apply, Derivation.smul_apply,
        correctionConnection, oscillatorConnection, pairDerivation, mkDerivation_X]
    | some index =>
      simp only [Derivation.add_apply, sum_apply, Derivation.smul_apply,
        correctionConnection, oscillatorConnection, pairDerivation, mkDerivation_X,
        Option.elim_some]
      module
  have compensation := congrArg (fun derivation => derivation polynomial) compensated
  simp only [Derivation.add_apply, sum_apply, Derivation.smul_apply] at compensation
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, smul_add, Finset.sum_add_distrib, add_mul]
  simp only [← smul_mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, singleton_sum]
  simp only [correctionPhysicalOperation, chargeMultiplier, LinearMap.add_apply,
    LinearMap.mulLeft_apply, Derivation.coeFn_coe, neg_smul]
  linear_combination compensation

private theorem operation_X_mul (D : LatticeData) (charge : Charge D)
    (coordinate : Option (Index D)) (polynomial : CorrectionPolynomial D) :
    correctionPhysicalOperation D charge (X coordinate * polynomial) =
      oscillatorConnection D (X coordinate) * polynomial +
        X coordinate * correctionPhysicalOperation D charge polynomial := by
  simp only [correctionPhysicalOperation, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
  ring

private theorem normalEvaluation_one (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) : normalEvaluation D hu charge 1 = chargedField D hu charge := by
  change polynomialEvaluation D hu charge ((optionEquivLeft ℂ (Index D)) 1) = _
  rw [map_one, ← Polynomial.monomial_zero_one,
    polynomialEvaluation_monomial, normalPolynomial_one, shiftLinear_zero]

private theorem normalEvaluation_C (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (scalar : ℂ) :
    normalEvaluation D hu charge (C scalar) = scalar • chargedField D hu charge := by
  rw [show (C scalar : CorrectionPolynomial D) = scalar • 1 by
      rw [MvPolynomial.smul_eq_C_mul, mul_one], map_smul, normalEvaluation_one]

private theorem charged_derivative_multiplier (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) :
    normalEvaluation D hu charge (chargeMultiplier D charge) =
      physicalDerivative D hu (chargedField D hu charge) := by
  have translated : LatticeSugawaraConformal.translation D (Finsupp.single charge 1) =
      originalFirstDescendant D (fun colour => (charge colour : ℂ)) charge := by
    simp [LatticeSugawaraConformal.translation_single, LatticeSugawaraConformal.chargePolynomial,
      originalFirstDescendant, Finsupp.single_finsetSum, Finsupp.smul_single]
  rw [← charged_physical_translation, translated, originalFirstDescendant_field]
  simp only [chargeMultiplier, map_sub, map_sum, map_smul, smul_sub, smul_smul,
    Finset.sum_sub_distrib]
  have colourEval (colour : Fin D.rank) :
      normalEvaluation D hu charge (X (some (colour, 0))) =
        normalInsertion D hu (colour, 0) (chargedField D hu charge) := by
    have evaluated := normalEvaluation_X_mul D hu charge (colour, 0) 1
    rw [mul_one, normalEvaluation_one] at evaluated
    exact evaluated
  have shiftEval : normalEvaluation D hu charge (X none) =
      shiftLinear D hu 1 (chargedField D hu charge) := by
    simpa only [mul_one, normalEvaluation_one] using normalEvaluation_shift_mul D hu charge 1
  simp only [colourEval, shiftEval]
  congr 1
  rw [← Finset.sum_smul]
  congr 1
  calc
    (chargeNorm D charge : ℂ) / 2 =
        (∑ colour, (charge colour : ℂ) * (bilinear D (unitCharge D colour) charge : ℂ)) / 2 := by
          rw [pairing_self]
    _ = ∑ colour, (charge colour : ℂ) * ((bilinear D (unitCharge D colour) charge : ℂ) / 2) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro colour member
      ring

private theorem normalEvaluation_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : CorrectionPolynomial D) :
    normalEvaluation D hu charge (correctionPhysicalOperation D charge polynomial) =
      physicalDerivativeLinear D hu (normalEvaluation D hu charge polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    have operation : correctionPhysicalOperation D charge (C scalar) =
        scalar • chargeMultiplier D charge := by
      simp [correctionPhysicalOperation, oscillatorConnection, MvPolynomial.derivation_C,
        MvPolynomial.smul_eq_C_mul, mul_comm]
    rw [operation, map_smul, charged_derivative_multiplier, normalEvaluation_C, map_smul]
    rfl
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]
  | mul_X polynomial coordinate previous =>
    rw [mul_comm polynomial, operation_X_mul, map_add]
    cases coordinate with
    | none =>
      simp only [oscillatorConnection, mkDerivation_X, neg_mul, map_neg, pow_two, mul_assoc,
        normalEvaluation_shift_mul, previous]
      rw [shift_add]
      change -(shiftLinear D hu 2 (normalEvaluation D hu charge polynomial)) +
        shiftLinear D hu 1 (physicalDerivative D hu (normalEvaluation D hu charge polynomial)) =
          physicalDerivative D hu (shiftLinear D hu 1 (normalEvaluation D hu charge polynomial))
      rw [shift_physical]
      abel
    | some index =>
      simp only [oscillatorConnection, mkDerivation_X, smul_mul_assoc, map_smul,
        normalEvaluation_X_mul, previous]
      change (sourceWeight D index : ℂ) •
          normalInsertion D hu (successorIndex D index) (normalEvaluation D hu charge polynomial) +
        normalInsertion D hu index (physicalDerivative D hu (normalEvaluation D hu charge polynomial)) =
          physicalDerivative D hu (normalInsertion D hu index (normalEvaluation D hu charge polynomial))
      have wordLaw := normalSequence_physical_derivative D hu [index]
        (normalEvaluation D hu charge polynomial)
      simpa [normalSequence, labelledRemainders, sourceWeight, successorIndex] using wordLaw.symm

private theorem correctedPolynomial_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) :
    correctedPolynomial D hu charge (LatticeSugawaraConformal.sectorTranslation D charge polynomial) =
      physicalDerivative D hu (correctedPolynomial D hu charge polynomial) := by
  have evaluation : normalEvaluation D hu charge (correctedSource D charge polynomial) =
      correctedPolynomial D hu charge polynomial := by
    simp only [normalEvaluation, correctedSource, polynomialEvaluation, correctedPolynomial,
      Corr, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply]
  simp only [correctedPolynomial, LinearMap.comp_apply]
  rw [Corr_sectorTranslation]
  change normalEvaluation D hu charge
    (correctionConnection D charge (correctedSource D charge polynomial) +
      ∑ colour : Fin D.rank, (charge colour : ℂ) •
        insertion D charge (colour, 0) (correctedSource D charge polynomial)) = _
  rw [correction_operation_identity, normalEvaluation_physical]
  change physicalDerivative D hu (normalEvaluation D hu charge (correctedSource D charge polynomial)) = _
  rw [evaluation]
  rfl

theorem Ytw_translation_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    (Ytw D hu (LatticeSugawaraConformal.translation D source)).coeff exponent vector =
      (((exponent + 2 : ℤ) : ℂ) / 2) • (Ytw D hu source).coeff (exponent + 2) vector := by
  have fields : Ytw D hu (LatticeSugawaraConformal.translation D source) =
      physicalDerivativeLinear D hu (Ytw D hu source) := by
    induction source using Finsupp.induction_linear with
    | zero => simp
    | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof]
    | single charge polynomial =>
      simp only [LatticeSugawaraConformal.translation, Ytw, Finsupp.lsum_single,
        LinearMap.comp_apply, Finsupp.lsingle_apply]
      exact correctedPolynomial_physical D hu charge polynomial
  have coefficient := congrArg (fun field => field.coeff exponent vector) fields
  exact coefficient

end
end D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.Ytw_translation_physical
