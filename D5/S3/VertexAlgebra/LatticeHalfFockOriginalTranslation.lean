/- GID: D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical translation of the native corrected Hahn field on every algebraic source. -/

/- Classical twisted-lattice calculus, adapted from the preserved OriginalTranslation
   source 0442324ef84346403888d5faa093adffdd3ec23b77918c37b81252c5404b008a
   and TranslationCalculus 8117eb5f8f5d301d5126a8d2fc054d22a1d7d2c314847a8b1699c89f5d123cd7.
   Charged ground and creation induction is imported from ChargedSeedPhysical.
   Copyright (c) 2025 Kalle Kytölä; additional half-integer implementation
   copyright (c) 2026. Apache 2.0. See the owning Scribe for classical sources. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedSeedPhysical
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation

/-! Physical translation on the original dependent algebraic tensor carrier. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFiniteCorrection LatticeHalfFockCorrectionTranslation
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField

def shiftField (D : LatticeData) (hu : IsUnit D.G.det) (s : ℕ) :
    NativeField D hu →ₗ[ℂ] NativeField D hu where
  toFun A :=
    { toFun := fun v => (HahnSeries.single (-2 * (s : ℤ)) (1 : ℂ)) • A v
      map_add' := by intro v w; rw [map_add, smul_add]
      map_smul' := by
        intro c v
        rw [map_smul]
        exact (smul_comm c (HahnSeries.single (-2 * (s : ℤ)) (1 : ℂ)) (A v)).symm }
  map_add' A B := by
    apply LinearMap.ext
    intro v
    change (HahnSeries.single (-2 * (s : ℤ)) (1 : ℂ)) • (A v + B v) = _
    exact smul_add _ _ _
  map_smul' c A := by
    apply LinearMap.ext
    intro v
    change (HahnSeries.single (-2 * (s : ℤ)) (1 : ℂ)) • (c • A v) =
      c • ((HahnSeries.single (-2 * (s : ℤ)) (1 : ℂ)) • A v)
    exact (smul_comm c (HahnSeries.single (-2 * (s : ℤ)) (1 : ℂ)) (A v)).symm

/- Native Hahn monomial action, consumed by shift and evaluator calculus. -/
private theorem shiftField_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℕ) (A : NativeField D hu) (e : ℤ) :
    (shiftField D hu s A).coeff e = A.coeff (e + 2 * (s : ℤ)) := by
  apply LinearMap.ext
  intro v
  change ((HahnModule.of ℂ).symm
    ((HahnSeries.single (-2 * (s : ℤ)) (1 : ℂ)) • A v)).coeff e = _
  have h := HahnModule.coeff_single_smul_vadd
    (r := (1 : ℂ)) (x := A v) (a := e + 2 * (s : ℤ)) (b := -2 * (s : ℤ))
  simpa only [HVertexOperator.coeff_apply_apply, vadd_eq_add, neg_add_cancel_left, one_smul,
    show -2 * (s : ℤ) + (e + 2 * (s : ℤ)) = e by ring] using h

theorem shiftField_coefficient_public (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℕ) (A : NativeField D hu) (e : ℤ) :
    (shiftField D hu s A).coeff e = A.coeff (e + 2 * (s : ℤ)) :=
  shiftField_coefficient D hu s A e

def correctedSum (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) :
    (ℕ →₀ Oscillator D) →ₗ[ℂ] NativeField D hu :=
  Finsupp.lsum ℂ (fun s => (shiftField D hu s).comp (polynomialField D hu a))

/-- The original finite Corr is composed with the actual normal supplier. -/
def correctedPolynomial (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) :
    Oscillator D →ₗ[ℂ] NativeField D hu :=
  (correctedSum D hu a).comp (Corr D a)

/-- All finite-charge original source states, acting on the full actual tensor module. -/
def correctedField (D : LatticeData) (hu : IsUnit D.G.det) :
    Carrier D →ₗ[ℂ] NativeField D hu :=
  Finsupp.lsum ℂ (correctedPolynomial D hu)


end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField

namespace D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
open LatticeHalfFockCorrectedField

private def physicalDerivative (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) : NativeField D hu :=
  HVertexOperator.of_coeff
    (fun exponent => ((((exponent + 2 : ℤ) : ℂ) / 2) • field.coeff (exponent + 2))) (by
      intro vector
      apply Set.IsWF.isPWO
      apply BddBelow.isWF
      refine ⟨((HahnModule.of ℂ).symm (field vector)).order - 2, ?_⟩
      intro exponent member
      by_contra outside
      have zero : field.coeff (exponent + 2) vector = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_order (by omega)
      apply member
      change ((((exponent + 2 : ℤ) : ℂ) / 2) • field.coeff (exponent + 2) vector) = 0
      rw [zero, smul_zero])


private abbrev insert (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) : NativeField D hu :=
  wordField D hu field [index]

private theorem jet_successor (order : ℕ) (mode : ℤ) :
    (order + 1 : ℂ) * jetScalar (order + 1) mode =
      (-(mode : ℂ) - 3 / 2 - (order : ℂ)) * jetScalar order mode := by
  have factorial : (order.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero order
  have successor : (order + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero order
  unfold jetScalar
  rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

private theorem singleton_physical_derivative (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) :
    physicalDerivative D hu (insert D hu index field) =
      (index.2 + 1 : ℂ) • insert D hu (index.1, index.2 + 1) field +
        insert D hu index (physicalDerivative D hu field) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  simp only [insert, physicalDerivative, HVertexOperator.coeff_of_coeff,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [wordField_coefficient, wordField_coefficient, wordField_coefficient]
  change (((exponent + 2 : ℤ) : ℂ) / 2) •
      (∑ᶠ m : ℤ × Unit, flatTerm D hu field [index] (exponent + 2) vector m) =
    (index.2 + 1 : ℂ) •
      (∑ᶠ m : ℤ × Unit, flatTerm D hu field [(index.1, index.2 + 1)] exponent vector m) +
      ∑ᶠ m : ℤ × Unit, flatTerm D hu (physicalDerivative D hu field) [index] exponent vector m
  have finiteSeed : Function.HasFiniteSupport (fun m : ℤ × Unit =>
      flatTerm D hu field [index] (exponent + 2) vector m) :=
    flatTerm_finite D hu field [index] (exponent + 2) vector
  have finiteNext : Function.HasFiniteSupport (fun m : ℤ × Unit =>
      flatTerm D hu field [(index.1, index.2 + 1)] exponent vector m) :=
    flatTerm_finite D hu field [(index.1, index.2 + 1)] exponent vector
  have finiteDerivative : Function.HasFiniteSupport (fun m : ℤ × Unit =>
      flatTerm D hu (physicalDerivative D hu field) [index] exponent vector m) :=
    flatTerm_finite D hu (physicalDerivative D hu field) [index] exponent vector
  rw [smul_finsum' _ finiteSeed, smul_finsum' _ finiteNext,
    ← finsum_add_distrib (finiteNext.fun_comp (smul_zero (index.2 + 1 : ℂ))) finiteDerivative]
  apply finsum_congr
  rintro ⟨mode, ⟨⟩⟩
  simp only [flatTerm, flatCoefficient, physicalDerivative, HVertexOperator.coeff_of_coeff]
  split_ifs <;>
    simp only [Module.End.mul_apply, jetCurrent, LinearMap.smul_apply, map_smul,
      smul_smul, Nat.cast_add, Nat.cast_one] <;>
    rw [show exponent + 2 * mode + 2 * ((index.2 : ℤ) + 1) + 3 =
        exponent + 2 + 2 * mode + 2 * index.2 + 3 by omega,
      show exponent + 2 * mode + 2 * index.2 + 3 + 2 =
        exponent + 2 + 2 * mode + 2 * index.2 + 3 by omega,
      ← add_smul, jet_successor] <;>
    congr 1 <;> push_cast <;> ring

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
    shiftField D hu first (shiftField D hu second field) =
      shiftField D hu (first + second) field := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [shiftField_coefficient, shiftField_coefficient, shiftField_coefficient]
  rw [show exponent + 2 * (first : ℤ) + 2 * (second : ℤ) =
      exponent + 2 * ((first + second : ℕ) : ℤ) by push_cast; ring]

private theorem shift_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) :
    physicalDerivative D hu (shiftField D hu 1 field) =
      shiftField D hu 1 (physicalDerivative D hu field) - shiftField D hu 2 field := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply]
  rw [physicalDerivative, HVertexOperator.coeff_of_coeff,
    shiftField_coefficient, shiftField_coefficient, shiftField_coefficient]
  change (((exponent + 2 : ℤ) : ℂ) / 2) • field.coeff (exponent + 2 + 2) vector =
    (((exponent + 2 + 2 : ℤ) : ℂ) / 2) • field.coeff (exponent + 2 + 2) vector -
      field.coeff (exponent + 4) vector
  rw [show exponent + 2 + 2 = exponent + 4 by omega]
  push_cast
  module

private theorem shift_insertion (D : LatticeData) (hu : IsUnit D.G.det)
    (shift : ℕ) (index : Index D) (field : NativeField D hu) :
    shiftField D hu shift (insert D hu index field) =
      insert D hu index (shiftField D hu shift field) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [shiftField_coefficient]
  simp only [insert, wordField_coefficient]
  apply finsum_congr
  rintro ⟨mode, ⟨⟩⟩
  simp only [flatTerm, flatCoefficient, shiftField_coefficient]
  rw [show exponent + 2 * (shift : ℤ) + 2 * mode + 2 * index.2 + 3 =
      exponent + 2 * mode + 2 * index.2 + 3 + 2 * (shift : ℤ) by ring]

private def polynomialEvaluation (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) : Polynomial (Oscillator D) →ₗ[ℂ] NativeField D hu :=
  (correctedSum D hu charge).comp (shiftCoefficients D)

private theorem polynomialEvaluation_monomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (shift : ℕ) (polynomial : Oscillator D) :
    polynomialEvaluation D hu charge (Polynomial.monomial shift polynomial) =
      shiftField D hu shift (polynomialField D hu charge polynomial) := by
  have coefficient : shiftCoefficients D (Polynomial.monomial shift polynomial) =
      Finsupp.single shift polynomial := by
    ext degree
    simp [shiftCoefficients, Polynomial.coeff_monomial]
  simp only [polynomialEvaluation, correctedSum, LinearMap.comp_apply, coefficient, Finsupp.lsum_single]

private theorem polynomialEvaluation_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Polynomial (Oscillator D)) :
    polynomialEvaluation D hu charge (Polynomial.X * polynomial) =
      shiftField D hu 1 (polynomialEvaluation D hu charge polynomial) := by
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
      singletonLinear D hu index (polynomialEvaluation D hu charge polynomial) := by
  induction polynomial using Polynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [mul_add, map_add, firstProof, secondProof]
  | monomial shift polynomial =>
    rw [Polynomial.C_mul_monomial, polynomialEvaluation_monomial,
      polynomialEvaluation_monomial, polynomialField_X_mul]
    exact shift_insertion D hu shift index _

private def normalEvaluation (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    CorrectionPolynomial D →ₗ[ℂ] NativeField D hu :=
  (polynomialEvaluation D hu charge).comp (optionEquivLeft ℂ (Index D)).toLinearMap

private theorem normalEvaluation_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (polynomial : CorrectionPolynomial D) :
    normalEvaluation D hu charge (X (some index) * polynomial) =
      singletonLinear D hu index (normalEvaluation D hu charge polynomial) := by
  simp only [normalEvaluation, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul, optionEquivLeft_X_some]
  exact polynomialEvaluation_C_X_mul D hu charge index _

private theorem normalEvaluation_shift_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : CorrectionPolynomial D) :
    normalEvaluation D hu charge (X none * polynomial) =
      shiftField D hu 1 (normalEvaluation D hu charge polynomial) := by
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
  have polynomialOne : polynomialField D hu charge 1 = chargedField D hu charge := by
    have basis := (MvPolynomial.basisMonomials (Index D) ℂ).constr_basis ℂ
      (fun a => chargedWordField D hu charge (occurrences D a)) 0
    have emptyWord : occurrences D (0 : Index D →₀ ℕ) = [] := by simp [occurrences]
    change polynomialField D hu charge (MvPolynomial.monomial 0 1) =
      wordField D hu (chargedField D hu charge) (occurrences D 0) at basis
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1, emptyWord] at basis
    rw [basis]
    apply HVertexOperator.coeff_inj
    funext exponent
    apply LinearMap.ext
    intro vector
    rw [wordField_coefficient]
    change (∑ᶠ _ : Unit, (chargedField D hu charge).coeff exponent vector) = _
    exact finsum_unique _
  change polynomialEvaluation D hu charge ((optionEquivLeft ℂ (Index D)) 1) = _
  rw [map_one, ← Polynomial.monomial_zero_one, polynomialEvaluation_monomial,
    polynomialOne]
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [shiftField_coefficient]
  simp

private theorem normalEvaluation_C (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (scalar : ℂ) :
    normalEvaluation D hu charge (C scalar) = scalar • chargedField D hu charge := by
  rw [show (C scalar : CorrectionPolynomial D) = scalar • 1 by
      rw [MvPolynomial.smul_eq_C_mul, mul_one], map_smul, normalEvaluation_one]

private theorem charged_seed_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) :
    (∑ colour : Fin D.rank, (charge colour : ℂ) •
      insert D hu (colour, 0) (chargedField D hu charge)) -
        ((chargeNorm D charge : ℂ) / 2) • shiftField D hu 1 (chargedField D hu charge) =
      physicalDerivative D hu (chargedField D hu charge) := by
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  simp only [map_sub, map_sum, map_smul, Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    physicalDerivative, HVertexOperator.coeff_of_coeff, insert]
  rw [shiftField_coefficient]
  simpa only [chargedField, HVertexOperator.coeff_of_coeff, Nat.cast_one, mul_one] using
    LatticeHalfFockChargedSeedPhysical.charged_seed_physical_coefficient
      D hu charge exponent vector

private theorem charged_derivative_multiplier (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) :
    normalEvaluation D hu charge (chargeMultiplier D charge) =
      physicalDerivative D hu (chargedField D hu charge) := by
  have some_variable (i : Index D) : normalEvaluation D hu charge (X (some i)) =
      singletonLinear D hu i (chargedField D hu charge) := by
    simpa only [mul_one, normalEvaluation_one] using
      normalEvaluation_X_mul D hu charge i 1
  have shift_variable : normalEvaluation D hu charge (X none) =
      shiftField D hu 1 (chargedField D hu charge) := by
    simpa only [mul_one, normalEvaluation_one] using
      normalEvaluation_shift_mul D hu charge 1
  simp only [chargeMultiplier, map_sub, map_sum, map_smul,
    some_variable, shift_variable]
  exact charged_seed_physical D hu charge

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
      change -(shiftField D hu 2 (normalEvaluation D hu charge polynomial)) +
        shiftField D hu 1 (physicalDerivative D hu (normalEvaluation D hu charge polynomial)) =
          physicalDerivative D hu (shiftField D hu 1 (normalEvaluation D hu charge polynomial))
      rw [shift_physical]
      abel
    | some index =>
      simp only [oscillatorConnection, mkDerivation_X, smul_mul_assoc, map_smul,
        normalEvaluation_X_mul, previous]
      change (sourceWeight D index : ℂ) •
          insert D hu (successorIndex D index)
            (normalEvaluation D hu charge polynomial) +
        insert D hu index
          (physicalDerivative D hu (normalEvaluation D hu charge polynomial)) =
          physicalDerivative D hu
            (insert D hu index (normalEvaluation D hu charge polynomial))
      rw [singleton_physical_derivative]
      simp only [sourceWeight, successorIndex, Nat.cast_add, Nat.cast_one]

private theorem correctedPolynomial_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) :
    correctedPolynomial D hu charge
        (LatticeSugawaraConformal.sectorTranslation D charge polynomial) =
      physicalDerivative D hu (correctedPolynomial D hu charge polynomial) := by
  have evaluation : normalEvaluation D hu charge (correctedSource D charge polynomial) =
      correctedPolynomial D hu charge polynomial := by
    simp only [normalEvaluation, correctedSource, polynomialEvaluation,
      correctedPolynomial, Corr, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      AlgEquiv.apply_symm_apply]
  simp only [correctedPolynomial, LinearMap.comp_apply]
  rw [Corr_sectorTranslation]
  change normalEvaluation D hu charge
    (correctionConnection D charge (correctedSource D charge polynomial) +
      ∑ colour : Fin D.rank, (charge colour : ℂ) •
        insertion D charge (colour, 0) (correctedSource D charge polynomial)) = _
  rw [correction_operation_identity, normalEvaluation_physical]
  change physicalDerivative D hu
      (normalEvaluation D hu charge (correctedSource D charge polynomial)) = _
  rw [evaluation]
  rfl

/-- Exact original-domain physical translation endpoint on the genuine
    corrected source field.  The source is arbitrary in `Carrier D`, the
    target is the actual dependent `ActualTensor D hu`, and every signed
    exponent is retained. -/
theorem correctedField_translation_physical (D : LatticeData) (hu : IsUnit D.G.det)
    (source : Carrier D) (e : ℤ) (v : ActualTensor D hu) :
    (correctedField D hu (LatticeSugawaraConformal.translation D source)).coeff e v =
      (((e + 2 : ℤ) : ℂ) / 2) •
        (correctedField D hu source).coeff (e + 2) v := by
  have fields : correctedField D hu (LatticeSugawaraConformal.translation D source) =
      physicalDerivativeLinear D hu (correctedField D hu source) := by
    induction source using Finsupp.induction_linear with
    | zero => simp
    | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof]
    | single charge polynomial =>
      simp only [LatticeSugawaraConformal.translation, correctedField,
        Finsupp.lsum_single, LinearMap.comp_apply, Finsupp.lsingle_apply]
      exact correctedPolynomial_physical D hu charge polynomial
  exact congrArg (fun field => field.coeff e v) fields

end D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
end


namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
/-- Coefficients of the canonical even Hahn shift. -/
theorem shiftField_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℕ) (A : NativeField D hu) (e : ℤ) :
    (shiftField D hu s A).coeff e = A.coeff (e + 2 * (s : ℤ)) :=
  shiftField_coefficient_public D hu s A e
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField

namespace D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
/-- Successive native jets keep the same signed current mode. -/
theorem native_jet_successor (order : ℕ) (mode : ℤ) :
    (order + 1 : ℂ) * jetScalar (order + 1) mode =
      (-(mode : ℂ) - 3 / 2 - (order : ℂ)) * jetScalar order mode :=
  jet_successor order mode
end D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

noncomputable section
namespace D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
open LatticeHalfFockCorrectedField LatticeHalfFockCurrentCorrection

private theorem normalEvaluation_shift_power_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (degree : ℕ) (polynomial : CorrectionPolynomial D) :
    normalEvaluation D hu charge (X none ^ degree * polynomial) =
      shiftField D hu degree (normalEvaluation D hu charge polynomial) := by
  induction degree with
  | zero =>
    simp only [pow_zero, one_mul]
    apply HVertexOperator.coeff_inj
    funext e
    rw [shiftField_coefficient]
    simp
  | succ degree previous =>
    rw [pow_succ', mul_assoc, normalEvaluation_shift_mul, previous, shift_add,
      Nat.add_comm 1 degree]

private theorem normalEvaluation_scalar_shift (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (scalar : ℂ) (degree : ℕ) (polynomial : CorrectionPolynomial D) :
    normalEvaluation D hu charge (C scalar * X none ^ degree * polynomial) =
      scalar • shiftField D hu degree (normalEvaluation D hu charge polynomial) := by
  rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul, map_smul,
    normalEvaluation_shift_power_mul]

private theorem normalEvaluation_correctionLift (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) :
    normalEvaluation D hu charge (correctionLift D charge polynomial) =
      correctedPolynomial D hu charge polynomial := rfl

private theorem pairDerivation_source_partials (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : Oscillator D) :
    pairDerivation D index (correctionLift D charge polynomial) =
      ∑ other ∈ polynomial.vars,
        pairPolynomial D index other * correctionLift D charge (pderiv other polynomial) := by
  classical
  let Q := correctionLift D charge polynomial
  let delta := pairDerivation D index
  have sum_apply (s : Finset (Option (Index D)))
      (f : Option (Index D) → Derivation ℂ (CorrectionPolynomial D) (CorrectionPolynomial D))
      (q : CorrectionPolynomial D) :
      (∑ x ∈ s, f x) q = ∑ x ∈ s, f x q := by
    have h := congrFun (map_sum
      (Derivation.coeFnAddMonoidHom (R := ℂ) (A := CorrectionPolynomial D)
        (M := CorrectionPolynomial D)) f s) q
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using h
  have expansion : delta Q = ∑ x ∈ Q.vars, delta (X x) * pderiv x Q := by
    have h : delta Q = (∑ x ∈ Q.vars, delta (X x) • pderiv x) Q := by
      apply MvPolynomial.derivation_eq_of_forall_mem_vars
      intro x hx
      rw [sum_apply]
      simp [Derivation.smul_apply, pderiv_X, Pi.single_apply, apply_ite, hx]
    rw [sum_apply] at h
    simpa only [Derivation.smul_apply, smul_eq_mul] using h
  let U := Q.vars ∪ polynomial.vars.image (some : Index D → Option (Index D))
  have first : (∑ x ∈ Q.vars, delta (X x) * pderiv x Q) =
      ∑ x ∈ U, delta (X x) * pderiv x Q := by
    apply Finset.sum_subset Finset.subset_union_left
    intro x hx outside
    rw [pderiv_eq_zero_of_notMem_vars outside, mul_zero]
  have second : (∑ x ∈ polynomial.vars.image (some : Index D → Option (Index D)),
      delta (X x) * pderiv x Q) = ∑ x ∈ U, delta (X x) * pderiv x Q := by
    apply Finset.sum_subset Finset.subset_union_right
    intro x hx outside
    cases x with
    | none => simp [delta, pairDerivation, mkDerivation_X]
    | some other =>
      have absent : other ∉ polynomial.vars := by
        intro member
        exact outside (Finset.mem_image.mpr ⟨other, member, rfl⟩)
      change delta (X (some other)) *
        pderiv (some other) (correctionLift D charge polynomial) = 0
      rw [correctionLift_partial, pderiv_eq_zero_of_notMem_vars absent, map_zero, mul_zero]
  rw [expansion, first, ← second, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro other member
    rw [show delta (X (some other)) = pairPolynomial D index other from
      pairDerivation_variable D index other]
    rw [correctionLift_partial]
  · intro x hx y hy equal
    exact Option.some.inj equal

private theorem correctedPolynomial_insertion_partials (D : LatticeData)
    (hu : IsUnit D.G.det) (charge : Charge D) (index : Index D) (polynomial : Oscillator D) :
    correctedPolynomial D hu charge (polynomial * X index) =
      singletonLinear D hu index (correctedPolynomial D hu charge polynomial) +
        (halfBinomial (sourceWeight D index) *
          (bilinear D (unitCharge D index.1) charge : ℂ)) •
          shiftField D hu (sourceWeight D index) (correctedPolynomial D hu charge polynomial) +
        ∑ other ∈ polynomial.vars,
          (pairScalar (sourceWeight D index) (sourceWeight D other) *
            (D.G index.1 other.1 : ℂ)) •
            shiftField D hu (sourceWeight D index + sourceWeight D other)
              (correctedPolynomial D hu charge (pderiv other polynomial)) := by
  rw [← normalEvaluation_correctionLift, correctionLift_X_mul]
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, add_mul, pairDerivation_source_partials, map_add, map_sum,
    singletonPolynomial, pairPolynomial, normalEvaluation_X_mul,
    normalEvaluation_scalar_shift, normalEvaluation_correctionLift]

end D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
end


noncomputable section
namespace D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
open LatticeHalfFockCorrectedField LatticeHalfFockCurrentCorrection
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents

private theorem correctedPolynomial_pair_modes (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (polynomial : Oscillator D) (bound : ℕ)
    (bounded : ∀ other ∈ polynomial.vars, sourceWeight D other ≤ bound) :
    (∑ other ∈ polynomial.vars,
      (pairScalar (sourceWeight D index) (sourceWeight D other) *
        (D.G index.1 other.1 : ℂ)) •
        shiftField D hu (sourceWeight D index + sourceWeight D other)
          (correctedPolynomial D hu charge (pderiv other polynomial))) =
    ∑ r ∈ Finset.range bound,
      (((sourceWeight D index : ℂ) * halfBinomial (sourceWeight D index) *
        halfBinomial (r + 1)) / ((sourceWeight D index : ℂ) + ((r + 1 : ℕ) : ℂ))) •
        shiftField D hu (sourceWeight D index + (r + 1))
          (correctedPolynomial D hu charge
            (neutralPolynomialMode D index.1 charge ((r : ℤ) + 1) polynomial)) := by
  classical
  have subset : polynomial.vars ⊆ (Finset.univ : Finset (Fin D.rank)) ×ˢ Finset.range bound := by
    intro other member
    have h := bounded other member
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by
      unfold sourceWeight at h
      omega)⟩
  rw [Finset.sum_subset subset (by
    intro other member outside
    rw [pderiv_eq_zero_of_notMem_vars outside, map_zero, map_zero, smul_zero])]
  rw [Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro r member
  rw [neutralPolynomialMode_positive]
  simp only [LinearMap.smul_apply, weightedPartial, LinearMap.sum_apply,
    Derivation.coeFn_coe, map_smul, map_sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro colour member
  have denominator : ((sourceWeight D index : ℂ) + ((r + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show sourceWeight D index + (r + 1) ≠ 0 by
      unfold sourceWeight
      omega)
  simp only [sourceWeight, Nat.cast_add, Nat.cast_one] at denominator
  congr 1
  simp only [sourceWeight, pairScalar, Nat.cast_add, Nat.cast_one]
  field_simp [denominator]
  <;> ring

private theorem insertion_zero_scalar (D : LatticeData) (index : Index D) :
    ((sourceWeight D index : ℂ) * halfBinomial (sourceWeight D index) * halfBinomial 0 /
      ((sourceWeight D index : ℂ) + (0 : ℂ))) = halfBinomial (sourceWeight D index) := by
  have positive : (sourceWeight D index : ℂ) ≠ 0 := by
    exact_mod_cast (show sourceWeight D index ≠ 0 by
      unfold sourceWeight
      omega)
  have zero : halfBinomial 0 = 1 := by norm_num [halfBinomial]
  rw [zero, mul_one, add_zero]
  exact mul_div_cancel_left₀ _ positive

private theorem correctedPolynomial_insertion_modes (D : LatticeData)
    (hu : IsUnit D.G.det) (charge : Charge D) (index : Index D) (polynomial : Oscillator D)
    (bound : ℕ) (bounded : ∀ other ∈ polynomial.vars, sourceWeight D other ≤ bound) :
    correctedPolynomial D hu charge (polynomial * X index) =
      singletonLinear D hu index (correctedPolynomial D hu charge polynomial) +
        ∑ n ∈ Finset.range (bound + 1),
          (((sourceWeight D index : ℂ) * halfBinomial (sourceWeight D index) *
            halfBinomial n) / ((sourceWeight D index : ℂ) + (n : ℂ))) •
            shiftField D hu (sourceWeight D index + n)
              (correctedPolynomial D hu charge
                (neutralPolynomialMode D index.1 charge (n : ℤ) polynomial)) := by
  rw [correctedPolynomial_insertion_partials,
    correctedPolynomial_pair_modes D hu charge index polynomial bound bounded,
    Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.add_zero, insertion_zero_scalar,
    neutralPolynomialMode, lt_self_iff_false, ite_false, ite_true, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul, smul_smul]
  abel

private theorem source_variable_bound (D : LatticeData) (b : Carrier D)
    (charge : Charge D) (supported : charge ∈ b.support) (other : Index D)
    (occurs : other ∈ (b charge).vars) :
    sourceWeight D other ≤ vectorFrequencyBound D b := by
  exact le_trans (Finset.le_sup (f := fun u : Index D => u.2 + 1) occurs)
    (Finset.le_sup (f := fun a => polynomialFrequencyBound D (b a)) supported)

end D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockOriginalTranslation

/-- Negative current insertion on every finite-charge source, with the cutoff
    taken on that original source and equality on the whole actual tensor field. -/
theorem correctedField_negative_current_insertion
    (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (b : Carrier D) :
    let m : ℕ := LatticeHalfFockFiniteCorrection.sourceWeight D index
    let N : ℕ := LatticeSugawaraCurrents.vectorFrequencyBound D b + 1
    correctedField D hu (LatticeFiniteNegativeGeneration.neutralMode D index.1 (-(m : ℤ)) b) =
      LatticeHalfFockFockNormalField.singletonLinear D hu index (correctedField D hu b) +
        ∑ n ∈ Finset.range N,
          (((m : ℂ) * LatticeHalfFockFiniteCorrection.halfBinomial m *
              LatticeHalfFockFiniteCorrection.halfBinomial n) / ((m : ℂ) + (n : ℂ))) •
            shiftField D hu (m + n)
              (correctedField D hu
                (LatticeFiniteNegativeGeneration.neutralMode D index.1 (n : ℤ) b)) := by
  classical
  dsimp only
  have negative (charge : Charge D) :
      neutralPolynomialMode D index.1 charge (-(sourceWeight D index : ℤ)) =
        LinearMap.mulLeft ℂ (X index) := by
    have frequency : -(sourceWeight D index : ℤ) = -(index.2 : ℤ) - 1 := by
      simp only [sourceWeight, Nat.cast_add, Nat.cast_one]
      ring
    rw [frequency, neutralPolynomialMode_negative]
  have expansion : b = ∑ charge ∈ b.support, Finsupp.single charge (b charge) := by
    exact b.sum_single.symm
  conv_lhs => rw [expansion]
  rw [map_sum, map_sum]
  simp only [neutralMode_single, correctedField, Finsupp.lsum_single,
    negative, LinearMap.mulLeft_apply, mul_comm (X index)]
  have recurrences : ∀ charge ∈ b.support,
      correctedPolynomial D hu charge (b charge * X index) =
        singletonLinear D hu index (correctedPolynomial D hu charge (b charge)) +
          ∑ n ∈ Finset.range (vectorFrequencyBound D b + 1),
            (((sourceWeight D index : ℂ) * halfBinomial (sourceWeight D index) *
              halfBinomial n) / ((sourceWeight D index : ℂ) + (n : ℂ))) •
              shiftField D hu (sourceWeight D index + n)
                (correctedPolynomial D hu charge
                  (neutralPolynomialMode D index.1 charge (n : ℤ) (b charge))) := by
    intro charge supported
    exact correctedPolynomial_insertion_modes D hu charge index (b charge)
      (vectorFrequencyBound D b) (source_variable_bound D b charge supported)
  simp_rw [Finset.sum_congr rfl recurrences]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  apply congrArg₂ (· + ·)
  · rw [← map_sum]
    rfl
  · apply Finset.sum_congr rfl
    intro n member
    rw [← Finset.smul_sum, ← map_sum]
    apply congrArg (fun F : NativeField D hu =>
      (((sourceWeight D index : ℂ) * halfBinomial (sourceWeight D index) *
        halfBinomial n) / ((sourceWeight D index : ℂ) + (n : ℂ))) •
          shiftField D hu (sourceWeight D index + n) F)
    rw [neutralMode, Finsupp.lsum_apply]
    change (∑ charge ∈ b.support, _) =
      (Finsupp.lsum ℂ (correctedPolynomial D hu))
        (∑ charge ∈ b.support, Finsupp.single charge
          (neutralPolynomialMode D index.1 charge (n : ℤ) (b charge)))
    rw [map_sum]
    simp only [Finsupp.lsum_single]

end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
end
