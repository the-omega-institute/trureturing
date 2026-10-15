/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeReflection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native half-coordinate jet reflection and finite charged descendant transposes. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Charged
import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant
import Mathlib.Algebra.BigOperators.NatAntidiagonal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockAllStateField
open LatticeHalfFockFiniteCorrection
open GolayLeech.ExplicitLeechLattice TwistedGround.NativeHyperbolicActions
open TwistedGround.NativeOrbit TwistedGround.NativeSymmetricForm
open scoped BigOperators TensorProduct

noncomputable section

def jetReflectionScalar (order reduced : ℕ) : ℂ :=
  (-1 : ℂ) ^ (order + 1) * ((order + 1).choose (reduced + 1) : ℂ)

private theorem jetScalar_choose (order : ℕ) (mode : ℤ) :
    jetScalar order mode = Ring.choose (-(mode : ℂ) - 3 / 2) order := by
  rw [Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval, Polynomial.aeval_def,
    ← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range]
  simp only [jetScalar, smul_eq_mul, div_eq_mul_inv]
  rw [mul_comm]

private theorem jetScalar_reflection (order : ℕ) (mode : ℤ) :
    -jetScalar order (-mode - 1) =
      ∑ reduced ∈ Finset.range (order + 1),
        jetReflectionScalar order reduced * jetScalar reduced mode := by
  have reflected : -((-mode - 1 : ℤ) : ℂ) - 3 / 2 =
      -((-(mode : ℂ) - 3 / 2) + 2) := by push_cast; ring
  rw [jetScalar_choose, reflected, Ring.choose_neg]
  have shift : (-(mode : ℂ) - 3 / 2) + 2 + order - 1 =
      (-(mode : ℂ) - 3 / 2) + ((order + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [shift, Ring.add_choose_eq order (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro reduced membership
  have within : reduced ≤ order := by simpa using Finset.mem_range.mp membership
  have choose : (order + 1).choose (order - reduced) =
      (order + 1).choose (reduced + 1) := by
    rw [← Nat.choose_symm (show reduced + 1 ≤ order + 1 by omega)]
    congr 1
    omega
  rw [Ring.choose_natCast, choose, ← jetScalar_choose]
  simp only [jetReflectionScalar, pow_succ]
  ring

private theorem jet_current_source_reflection (axis : Fin data.rank) (order : ℕ)
    (mode : ℤ) (first second : NativeTensor) :
    tensorPairing (jetCurrent data determinantUnit (axis, order) mode first) second =
      ∑ reduced ∈ Finset.range (order + 1), jetReflectionScalar order reduced *
        tensorPairing first
          (jetCurrent data determinantUnit (axis, reduced) (-mode - 1) second) := by
  simp only [jetCurrent, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  rw [tensor_current_adjoint]
  have reflection := jetScalar_reflection order (-mode - 1)
  have index : -(-mode - 1) - 1 = mode := by omega
  rw [index] at reflection
  rw [mul_neg, ← neg_mul, reflection, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro reduced membership
  ring

def groundReflection (charge : Charge data) : Module.End ℂ NativeTensor :=
  TensorProduct.map (LinearMap.id : Module.End ℂ (Oscillator data))
    (groundAction data determinantUnit (-charge) *
      groundAction data determinantUnit (-charge))

def oppositeChargedField (charge : Charge data) : NativeField data determinantUnit :=
  LinearMap.comp (chargedField data determinantUnit charge) (groundReflection charge)

def nativeOppositeYtw : Carrier data →ₗ[ℂ] NativeField data determinantUnit :=
  Finsupp.lsum ℂ (fun charge =>
    (correctedPolynomial data determinantUnit charge).compl₂ (groundReflection charge))

private theorem opposite_charged_coefficient (charge : Charge data) (exponent : ℤ)
    (state : NativeTensor) :
    (oppositeChargedField charge).coeff exponent state =
      chargeScalar data charge • TensorProduct.map
        (oscillatorCoefficient data charge exponent)
        (epsilon data charge (-charge) • groundAction data determinantUnit (-charge)) state := by
  have groundProduct : groundAction data determinantUnit charge *
      (groundAction data determinantUnit (-charge) *
        groundAction data determinantUnit (-charge)) =
      epsilon data charge (-charge) • groundAction data determinantUnit (-charge) := by
    rw [← mul_assoc, LatticeHalfFockGroundProducts.ground_action_product, add_neg_cancel]
    have zeroAction : groundAction data determinantUnit 0 =
        (1 : Module.End ℂ NativeGround) := by
      change groundRepresentation data determinantUnit 1 = 1
      exact map_one _
    rw [zeroAction, smul_mul_assoc, one_mul]
  change chargedCoefficient data determinantUnit charge exponent
    (TensorProduct.map LinearMap.id
      (groundAction data determinantUnit (-charge) *
        groundAction data determinantUnit (-charge)) state) = _
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, chargedCoefficient,
      LinearMap.smul_apply, TensorProduct.map_tmul]
    congr 2
    exact congrArg (fun operator : Module.End ℂ NativeGround => operator ground) groundProduct
  | add first second firstProof secondProof =>
    simp only [map_add, smul_add, firstProof, secondProof]

private theorem charged_opposite_pairing (charge : Charge data) (exponent : ℤ)
    (first second : NativeTensor) :
    tensorPairing (chargedCoefficient data determinantUnit charge exponent first) second =
      tensorPairing first ((oppositeChargedField charge).coeff
        (-2 * chargeNorm data charge - exponent) second) := by
  rw [opposite_charged_coefficient, map_smul, tensor_charged_adjoint]
  rfl

private theorem flat_jet_charged_source_reflection (charge : Charge data)
    (axis : Fin data.rank) (order : ℕ) (exponent mode : ℤ)
    (first second : NativeTensor) :
    tensorPairing
      (flatTerm data determinantUnit (chargedField data determinantUnit charge)
        [(axis, order)] exponent first (mode, ())) second =
      ∑ reduced ∈ Finset.range (order + 1), jetReflectionScalar order reduced *
        tensorPairing first
          (flatTerm data determinantUnit (oppositeChargedField charge)
            [(axis, reduced)]
            (-2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4)
            second (-mode - 1, ())) := by
  have index (reduced : ℕ) :
      -2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4 +
        2 * (-mode - 1) + 2 * reduced + 3 =
      -2 * chargeNorm data charge - (exponent + 2 * mode + 2 * order + 3) := by ring
  by_cases negative : mode < 0
  · have reflectedPositive : ¬ -mode - 1 < 0 := by omega
    simp only [flatTerm, flatCoefficient, if_pos negative, Module.End.mul_apply]
    rw [jet_current_source_reflection]
    apply Finset.sum_congr rfl
    intro reduced membership
    rw [chargedField, HVertexOperator.coeff_of_coeff, charged_opposite_pairing]
    simp only [flatTerm, flatCoefficient, if_neg reflectedPositive, Module.End.mul_apply]
    rw [index]
  · have reflectedNegative : -mode - 1 < 0 := by omega
    simp only [flatTerm, flatCoefficient, if_neg negative, Module.End.mul_apply,
      chargedField, HVertexOperator.coeff_of_coeff]
    rw [charged_opposite_pairing, jet_current_source_reflection]
    apply Finset.sum_congr rfl
    intro reduced membership
    simp only [flatTerm, flatCoefficient, if_pos reflectedNegative, Module.End.mul_apply]
    rw [index]

private theorem paired_flat_jet_finite (field : NativeField data determinantUnit)
    (axis : Fin data.rank) (order : ℕ) (exponent : ℤ)
    (first second : NativeTensor) :
    Function.HasFiniteSupport (fun mode : ℤ => tensorPairing first
      (flatTerm data determinantUnit field [(axis, order)] exponent second (mode, ()))) :=
  ((flatTerm_finite data determinantUnit field [(axis, order)] exponent second).comp_of_injective
    (show Function.Injective (fun mode : ℤ => (mode, ())) from by
      intro left right equal; exact congrArg Prod.fst equal)).fun_comp (map_zero _)

private theorem normal_jet_charged_source_reflection (charge : Charge data)
    (axis : Fin data.rank) (order : ℕ) (exponent : ℤ)
    (first second : NativeTensor) :
    tensorPairing
      ((normalInsertion data determinantUnit (axis, order)
        (chargedField data determinantUnit charge)).coeff exponent first) second =
      ∑ reduced ∈ Finset.range (order + 1), jetReflectionScalar order reduced *
        tensorPairing first
          ((normalInsertion data determinantUnit (axis, reduced)
            (oppositeChargedField charge)).coeff
            (-2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4)
            second) := by
  classical
  rw [normalInsertion_integer_modes]
  change tensorPairing.flip second
    (∑ᶠ mode : ℤ, flatTerm data determinantUnit
      (chargedField data determinantUnit charge) [(axis, order)] exponent first (mode, ())) = _
  have leftFinite : Function.HasFiniteSupport (fun mode : ℤ =>
      flatTerm data determinantUnit (chargedField data determinantUnit charge)
        [(axis, order)] exponent first (mode, ())) := by
    simpa only [Function.comp_def] using
      (flatTerm_finite data determinantUnit (chargedField data determinantUnit charge)
        [(axis, order)] exponent first).comp_of_injective
          (show Function.Injective (fun mode : ℤ => (mode, ())) from by
            intro left right equal; exact congrArg Prod.fst equal)
  rw [map_finsum (tensorPairing.flip second) leftFinite]
  change (∑ᶠ mode : ℤ, tensorPairing
    (flatTerm data determinantUnit (chargedField data determinantUnit charge)
      [(axis, order)] exponent first (mode, ())) second) = _
  conv_lhs =>
    arg 1
    ext mode
    rw [flat_jet_charged_source_reflection charge axis order exponent mode first second]
  let terms : ℕ → ℤ → ℂ := fun reduced mode => jetReflectionScalar order reduced *
    tensorPairing first
      (flatTerm data determinantUnit (oppositeChargedField charge) [(axis, reduced)]
        (-2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4)
        second (mode, ()))
  have finite (reduced : ℕ) : Function.HasFiniteSupport (terms reduced) :=
    (paired_flat_jet_finite (oppositeChargedField charge) axis reduced _ first second).fun_comp
      (show (jetReflectionScalar order reduced * (0 : ℂ)) = 0 by simp)
  change (∑ᶠ mode : ℤ, ∑ reduced ∈ Finset.range (order + 1),
    terms reduced (-mode - 1)) = _
  have reflectedFinite (reduced : ℕ) :
      Function.HasFiniteSupport (fun mode : ℤ => terms reduced (-mode - 1)) := by
    simpa only [Function.comp_def] using (finite reduced).comp_of_injective
      (show Function.Injective (fun mode : ℤ => -mode - 1) from by
        intro left right equal; dsimp at equal; omega)
  rw [finsum_sum_comm (Finset.range (order + 1))
    (fun mode : ℤ => fun reduced => terms reduced (-mode - 1))
    (fun reduced membership => reflectedFinite reduced)]
  apply Finset.sum_congr rfl
  intro reduced membership
  let reflect : ℤ ≃ ℤ := {
    toFun := fun mode => -mode - 1
    invFun := fun mode => -mode - 1
    left_inv := by intro mode; dsimp; omega
    right_inv := by intro mode; dsimp; omega }
  rw [show (∑ᶠ mode : ℤ, terms reduced (-mode - 1)) = ∑ᶠ mode : ℤ, terms reduced mode by
    exact finsum_comp_equiv reflect]
  rw [normalInsertion_integer_modes]
  have rightFinite : Function.HasFiniteSupport (fun mode : ℤ =>
      flatTerm data determinantUnit (oppositeChargedField charge) [(axis, reduced)]
        (-2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4)
        second (mode, ())) := by
    simpa only [Function.comp_def] using
      (flatTerm_finite data determinantUnit (oppositeChargedField charge) [(axis, reduced)]
        (-2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4)
        second).comp_of_injective
          (show Function.Injective (fun mode : ℤ => (mode, ())) from by
            intro left right equal; exact congrArg Prod.fst equal)
  rw [map_finsum (tensorPairing first) rightFinite]
  exact (mul_finsum' _ _ (paired_flat_jet_finite (oppositeChargedField charge) axis reduced _
    first second)).symm

private theorem correction_single_jet (charge : Charge data) (axis : Fin data.rank)
    (order : ℕ) :
    Corr data charge (MvPolynomial.X (axis, order)) =
      Finsupp.single 0 (MvPolynomial.X (axis, order)) +
        Finsupp.single (order + 1)
          ((halfBinomial (order + 1) *
            (bilinear data (unitCharge data axis) charge : ℂ)) • (1 : Oscillator data)) := by
  have source := Corr_monomial_enumeration data charge
    (Finsupp.single (axis, order) 1) [(axis, order)] (by
      simp [LatticeAllStateField.occurrences])
  change Corr data charge (MvPolynomial.X (axis, order)) = _ at source
  have correction : MvPolynomial.optionEquivLeft ℂ (Index data)
      (correctionWord data charge [(axis, order)]) =
      Polynomial.C (MvPolynomial.X (axis, order)) +
        Polynomial.C ((halfBinomial (order + 1) *
          (bilinear data (unitCharge data axis) charge : ℂ)) • (1 : Oscillator data)) *
            Polynomial.X ^ (order + 1) := by
    simp [correctionWord, insertion, singletonPolynomial, sourceWeight,
      MvPolynomial.smul_eq_C_mul]
  rw [source, correction]
  ext shift
  simp [shiftCoefficients, Finsupp.single_apply, eq_comm]

private theorem original_jet_field (charge : Charge data) (axis : Fin data.rank)
    (order : ℕ) :
    Ytw data determinantUnit (Finsupp.single charge (MvPolynomial.X (axis, order))) =
      normalInsertion data determinantUnit (axis, order)
        (chargedField data determinantUnit charge) +
      (halfBinomial (order + 1) *
        (bilinear data (unitCharge data axis) charge : ℂ)) •
        shiftLinear data determinantUnit (order + 1) (chargedField data determinantUnit charge) := by
  simp only [Ytw, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply]
  rw [correction_single_jet, map_add]
  simp [Finsupp.lsum_single, normalPolynomial_one, shiftLinear_zero]
  exact LatticeHalfFockFockNormalField.normalPolynomial_X data determinantUnit charge (axis, order)

private theorem current_ground_reflection (charge : Charge data) (axis : Fin data.rank)
    (mode : ℤ) (state : NativeTensor) :
    tensorCurrent data NativeGround axis mode (groundReflection charge state) =
      groundReflection charge (tensorCurrent data NativeGround axis mode state) := by
  induction state using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [groundReflection, tensorCurrent, tensorEnd, TensorProduct.map_tmul,
      LinearMap.id_apply]
  | add first second firstProof secondProof => simp only [map_add, firstProof, secondProof]

private theorem normalInsertion_ground_reflection (charge : Charge data)
    (axis : Fin data.rank) (order : ℕ) (exponent : ℤ) (state : NativeTensor) :
    (normalInsertion data determinantUnit (axis, order)
      (chargedField data determinantUnit charge)).coeff exponent (groundReflection charge state) =
    (normalInsertion data determinantUnit (axis, order)
      (oppositeChargedField charge)).coeff exponent state := by
  simp only [normalInsertion, HVertexOperator.coeff_of_coeff, normalCoefficient,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  apply finsum_congr
  intro offset
  simp only [positiveTerm, current_ground_reflection]
  rfl

private theorem opposite_jet_coefficient (charge : Charge data) (axis : Fin data.rank)
    (order : ℕ) (exponent : ℤ) (state : NativeTensor) :
    (nativeOppositeYtw (Finsupp.single charge (MvPolynomial.X (axis, order)))).coeff
      exponent state =
    (normalInsertion data determinantUnit (axis, order)
      (oppositeChargedField charge)).coeff exponent state +
      (halfBinomial (order + 1) *
        (bilinear data (unitCharge data axis) charge : ℂ)) •
        (oppositeChargedField charge).coeff (exponent + 2 * (order + 1)) state := by
  rw [nativeOppositeYtw, Finsupp.lsum_single]
  change (correctedPolynomial data determinantUnit charge
    (MvPolynomial.X (axis, order))).coeff exponent (groundReflection charge state) = _
  rw [show correctedPolynomial data determinantUnit charge (MvPolynomial.X (axis, order)) =
    Ytw data determinantUnit (Finsupp.single charge (MvPolynomial.X (axis, order))) by
      simp [Ytw]]
  change (Ytw data determinantUnit
    (Finsupp.single charge (MvPolynomial.X (axis, order)))).coeff exponent
      (groundReflection charge state) = _
  rw [original_jet_field]
  change (normalInsertion data determinantUnit (axis, order)
    (chargedField data determinantUnit charge)).coeff exponent (groundReflection charge state) +
    (halfBinomial (order + 1) *
      (bilinear data (unitCharge data axis) charge : ℂ)) •
      (oppositeChargedField charge).coeff (exponent + 2 * (order + 1)) state = _
  rw [normalInsertion_ground_reflection]

private theorem opposite_charge_coefficient (charge : Charge data) (exponent : ℤ)
    (state : NativeTensor) :
    (nativeOppositeYtw (Finsupp.single charge 1)).coeff exponent state =
      (oppositeChargedField charge).coeff exponent state := by
  rw [nativeOppositeYtw, Finsupp.lsum_single]
  change (correctedPolynomial data determinantUnit charge 1).coeff exponent
    (groundReflection charge state) = _
  rw [show correctedPolynomial data determinantUnit charge 1 =
      chargedField data determinantUnit charge by simpa [Ytw] using
        (Ytw_charge data determinantUnit charge)]
  rfl

private theorem halfBinomial_choose (degree : ℕ) :
    halfBinomial degree = Ring.choose (-1 / 2 : ℂ) degree := by
  have scalar : halfBinomial degree = jetScalar degree (-1) := by
    simp only [halfBinomial, jetScalar]
    congr 1
    apply Finset.prod_congr rfl
    intro offset membership
    norm_num
  rw [scalar, jetScalar_choose]
  congr 1
  norm_num

private theorem singleton_correction_reflection (order : ℕ) :
    halfBinomial (order + 1) = (-1 : ℂ) ^ (order + 1) +
      ∑ reduced ∈ Finset.range (order + 1),
        jetReflectionScalar order reduced * halfBinomial (reduced + 1) := by
  rw [halfBinomial_choose]
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  rw [Ring.choose_neg]
  have index : (1 / 2 : ℂ) + ((order + 1 : ℕ) : ℂ) - 1 =
      -1 / 2 + ((order + 1 : ℕ) : ℂ) := by ring
  rw [index, Ring.add_choose_eq (order + 1) (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [Ring.choose_zero_right, Ring.choose_natCast, Nat.sub_zero, Nat.choose_self,
    Nat.cast_one, one_mul, Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast,
    mul_add, mul_one, Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro reduced membership
  have within : reduced + 1 ≤ order + 1 := by
    have := Finset.mem_range.mp membership
    omega
  have choose : (order + 1).choose (order + 1 - (reduced + 1)) =
      (order + 1).choose (reduced + 1) := Nat.choose_symm within
  rw [choose, ← halfBinomial_choose]
  simp only [jetReflectionScalar]
  ring

theorem original_jet_source_reflection (charge : Charge data) (axis : Fin data.rank)
    (order : ℕ) (exponent : ℤ) (first second : NativeTensor) :
    tensorPairing
      ((Ytw data determinantUnit
        (Finsupp.single charge (MvPolynomial.X (axis, order)))).coeff exponent first) second =
    (∑ reduced ∈ Finset.range (order + 1), jetReflectionScalar order reduced *
      tensorPairing first
        ((nativeOppositeYtw (Finsupp.single charge (MvPolynomial.X (axis, reduced)))).coeff
          (-2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4) second)) +
      ((-1 : ℂ) ^ (order + 1) * (bilinear data (unitCharge data axis) charge : ℂ)) *
        tensorPairing first ((nativeOppositeYtw (Finsupp.single charge 1)).coeff
          (-2 * chargeNorm data charge - exponent - 2 * order - 2) second) := by
  classical
  have reflectedIndex (reduced : ℕ) :
      -2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4 +
        2 * ((reduced : ℤ) + 1) =
      -2 * chargeNorm data charge - exponent - 2 * order - 2 := by push_cast; ring
  have scalarIndex : -2 * chargeNorm data charge -
      (exponent + 2 * ((order : ℤ) + 1)) =
      -2 * chargeNorm data charge - exponent - 2 * order - 2 := by push_cast; ring
  rw [original_jet_field]
  change tensorPairing
    ((normalInsertion data determinantUnit (axis, order)
      (chargedField data determinantUnit charge)).coeff exponent first +
        (halfBinomial (order + 1) *
          (bilinear data (unitCharge data axis) charge : ℂ)) •
          chargedCoefficient data determinantUnit charge (exponent + 2 * (order + 1)) first)
    second = _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [normal_jet_charged_source_reflection, charged_opposite_pairing, scalarIndex]
  conv_rhs =>
    arg 1
    arg 2
    ext reduced
    rw [opposite_jet_coefficient charge axis reduced
      (-2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4) second]
    rw [reflectedIndex reduced]
  rw [opposite_charge_coefficient]
  simp only [map_add, map_smul, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [singleton_correction_reflection]
  simp only [add_mul, Finset.sum_mul, mul_assoc]
  ring

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockBpZ.original_jet_source_reflection
