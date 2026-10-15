/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeReflection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native half-coordinate jet reflection and finite charged descendant transposes. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Charged
import D5.S3.VertexAlgebra.LatticeHalfFockFirstDescendant
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeed
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCorrectionWeight
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

private abbrev JetChoices : List (Index data) → Type
  | [] => Unit
  | index :: tail => Fin (index.2 + 1) × JetChoices tail

private instance jetChoicesFintype (word : List (Index data)) : Fintype (JetChoices word) := by
  induction word with
  | nil => exact inferInstanceAs (Fintype Unit)
  | cons index tail ih =>
    change Fintype (Fin (index.2 + 1) × JetChoices tail)
    letI := ih
    infer_instance

private def reducedWord : (word : List (Index data)) → JetChoices word → List (Index data)
  | [], _ => []
  | index :: tail, choice => (index.1, choice.1.val) :: reducedWord tail choice.2

private def reductionScalar : (word : List (Index data)) → JetChoices word → ℂ
  | [], _ => 1
  | index :: tail, choice =>
    jetReflectionScalar index.2 choice.1.val * reductionScalar tail choice.2

private def reflectInteger : ℤ ≃ ℤ where
  toFun mode := -mode - 1
  invFun mode := -mode - 1
  left_inv mode := by dsimp; omega
  right_inv mode := by dsimp; omega

private def reflectedModes : (word : List (Index data)) → (choice : JetChoices word) →
    ModeTuple data word ≃ ModeTuple data (reducedWord word choice)
  | [], _ => Equiv.refl Unit
  | _ :: tail, choice => Equiv.prodCongr reflectInteger (reflectedModes tail choice.2)

private theorem jet_current_choice_reflection (axis : Fin data.rank) (order : ℕ)
    (mode : ℤ) (first second : NativeTensor) :
    tensorPairing (jetCurrent data determinantUnit (axis, order) mode first) second =
      ∑ reduced : Fin (order + 1), jetReflectionScalar order reduced.val *
        tensorPairing first
          (jetCurrent data determinantUnit (axis, reduced.val) (-mode - 1) second) := by
  rw [jet_current_source_reflection]
  exact (Fin.sum_univ_eq_sum_range (fun reduced : ℕ => jetReflectionScalar order reduced *
    tensorPairing first (jetCurrent data determinantUnit (axis, reduced) (-mode - 1) second))
      (order + 1)).symm

private theorem flat_word_source_reflection (charge : Charge data)
    (word : List (Index data)) (exponent : ℤ) (first second : NativeTensor)
    (modes : ModeTuple data word) :
    tensorPairing (flatTerm data determinantUnit (chargedField data determinantUnit charge)
      word exponent first modes) second =
    ∑ choice : JetChoices word, reductionScalar word choice * tensorPairing first
      (flatTerm data determinantUnit (oppositeChargedField charge)
        (reducedWord word choice)
        (-2 * chargeNorm data charge - exponent - 2 * (wordWeight data word : ℤ) -
          2 * (wordWeight data (reducedWord word choice) : ℤ)) second
        (reflectedModes word choice modes)) := by
  classical
  induction word generalizing exponent first second with
  | nil =>
    simp only [JetChoices, reducedWord, reductionScalar, reflectedModes, flatTerm,
      flatCoefficient, wordWeight, List.map_nil, List.sum_nil, Nat.cast_zero,
      mul_zero, sub_zero, one_mul, Fintype.sum_unique, Equiv.refl_apply]
    rw [chargedField, HVertexOperator.coeff_of_coeff]
    exact charged_opposite_pairing charge exponent first second
  | cons index tail ih =>
    simp only [flatTerm] at ih
    rcases index with ⟨axis, order⟩
    rcases modes with ⟨mode, modes⟩
    have shift (reduced : ℕ) (choice : JetChoices tail) :
        -2 * chargeNorm data charge - exponent -
          2 * (wordWeight data ((axis, order) :: tail) : ℤ) -
          2 * (wordWeight data ((axis, reduced) :: reducedWord tail choice) : ℤ) +
          2 * (-mode - 1) + 2 * reduced + 3 =
        -2 * chargeNorm data charge - (exponent + 2 * mode + 2 * order + 3) -
          2 * (wordWeight data tail : ℤ) -
          2 * (wordWeight data (reducedWord tail choice) : ℤ) := by
      simp only [wordWeight, List.map_cons, List.sum_cons, sourceWeight, Nat.cast_add,
        Nat.cast_one]
      ring
    change _ = ∑ choice : Fin (order + 1) × JetChoices tail, _
    rw [Fintype.sum_prod_type]
    by_cases negative : mode < 0
    · have reflectedPositive : ¬ -mode - 1 < 0 := by omega
      simp only [flatTerm, flatCoefficient, if_pos negative, Module.End.mul_apply]
      rw [jet_current_choice_reflection]
      apply Finset.sum_congr rfl
      intro reduced _
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro choice _
      simp only [reductionScalar, reducedWord, reflectedModes, Equiv.prodCongr_apply,
        reflectInteger, Equiv.coe_fn_mk, Prod.map, flatTerm, flatCoefficient,
        if_neg reflectedPositive, Module.End.mul_apply]
      rw [shift]
      ring
    · have reflectedNegative : -mode - 1 < 0 := by omega
      simp only [flatTerm, flatCoefficient, if_neg negative, Module.End.mul_apply]
      rw [ih]
      conv_lhs =>
        arg 2
        ext choice
        rw [jet_current_choice_reflection]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro reduced _
      apply Finset.sum_congr rfl
      intro choice _
      simp only [reductionScalar, reducedWord, reflectedModes, Equiv.prodCongr_apply,
        reflectInteger, Equiv.coe_fn_mk, Prod.map, flatTerm, flatCoefficient,
        if_pos reflectedNegative, Module.End.mul_apply]
      rw [shift]
      ring

private theorem normal_word_source_reflection (charge : Charge data)
    (word : List (Index data)) (exponent : ℤ) (first second : NativeTensor) :
    tensorPairing ((normalWord data determinantUnit charge word).coeff exponent first) second =
    ∑ choice : JetChoices word, reductionScalar word choice * tensorPairing first
      ((normalSequence data determinantUnit (oppositeChargedField charge)
        (reducedWord word choice)).coeff
        (-2 * chargeNorm data charge - exponent - 2 * (wordWeight data word : ℤ) -
          2 * (wordWeight data (reducedWord word choice) : ℤ)) second) := by
  classical
  rw [normalWord_flattened]
  change tensorPairing.flip second (∑ᶠ modes : ModeTuple data word, _) = _
  rw [map_finsum _ (flatTerm_finite data determinantUnit
    (chargedField data determinantUnit charge) word exponent first)]
  change (∑ᶠ modes : ModeTuple data word, tensorPairing
    (flatTerm data determinantUnit (chargedField data determinantUnit charge)
      word exponent first modes) second) = _
  simp_rw [flat_word_source_reflection]
  let terms (choice : JetChoices word) (modes : ModeTuple data (reducedWord word choice)) : ℂ :=
    reductionScalar word choice * tensorPairing first
      (flatTerm data determinantUnit (oppositeChargedField charge) (reducedWord word choice)
        (-2 * chargeNorm data charge - exponent - 2 * (wordWeight data word : ℤ) -
          2 * (wordWeight data (reducedWord word choice) : ℤ)) second modes)
  have finite (choice : JetChoices word) : Function.HasFiniteSupport (terms choice) :=
    ((flatTerm_finite data determinantUnit (oppositeChargedField charge)
      (reducedWord word choice) _ second).fun_comp (map_zero _)).fun_comp (mul_zero _)
  have jointlyFinite (choice : JetChoices word) : Function.HasFiniteSupport
      (fun modes : ModeTuple data word => terms choice (reflectedModes word choice modes)) :=
    Function.HasFiniteSupport.comp_of_injective
      (f := terms choice) (g := fun modes => reflectedModes word choice modes)
      (reflectedModes word choice).injective (finite choice)
  change (∑ᶠ modes : ModeTuple data word,
    ∑ choice : JetChoices word, terms choice (reflectedModes word choice modes)) = _
  rw [finsum_sum_comm Finset.univ _ (fun choice _ => jointlyFinite choice)]
  apply Finset.sum_congr rfl
  intro choice _
  rw [finsum_comp_equiv (reflectedModes word choice)]
  rw [normalSequence_flattened, map_finsum _ (flatTerm_finite data determinantUnit
    (oppositeChargedField charge) (reducedWord word choice) _ second)]
  exact (mul_finsum' _ _ ((flatTerm_finite data determinantUnit
    (oppositeChargedField charge) (reducedWord word choice) _ second).fun_comp
      (map_zero _))).symm

private def reflectionFactor (index : Index data) (reduced : ℕ) : CorrectionPolynomial data :=
  MvPolynomial.C (jetReflectionScalar index.2 reduced) *
    MvPolynomial.X none ^ (index.2 - reduced)

private def jetSubstitution : CorrectionPolynomial data →ₐ[ℂ] CorrectionPolynomial data :=
  MvPolynomial.aeval (fun coordinate : Option (Index data) => coordinate.elim
    (MvPolynomial.X none) (fun index => ∑ reduced ∈ Finset.range (index.2 + 1),
      reflectionFactor index reduced * MvPolynomial.X (some (index.1, reduced))))

private theorem substitution_shift (degree : ℕ) :
    jetSubstitution (MvPolynomial.X none ^ degree) = MvPolynomial.X none ^ degree := by
  simp [jetSubstitution]

private theorem substitution_pair (first second : Index data) :
    jetSubstitution (pairPolynomial data first second) = pairPolynomial data first second := by
  simp [pairPolynomial, jetSubstitution]

private theorem reflected_pair_lift (first second : Index data) :
    pairPolynomial data first second =
    ∑ left ∈ Finset.range (first.2 + 1), ∑ right ∈ Finset.range (second.2 + 1),
      reflectionFactor first left * reflectionFactor second right *
        pairPolynomial data (first.1, left) (second.1, right) := by
  classical
  have scalar := pairScalar_reflection first.2 second.2
  change pairScalar (first.2 + 1) (second.2 + 1) =
    ∑ left ∈ Finset.range (first.2 + 1), ∑ right ∈ Finset.range (second.2 + 1),
      (jetReflectionScalar first.2 left * jetReflectionScalar second.2 right) *
        pairScalar (left + 1) (right + 1) at scalar
  have lifted := congrArg (fun value : ℂ => MvPolynomial.C
    (value * (data.G first.1 second.1 : ℂ)) *
      (MvPolynomial.X none : CorrectionPolynomial data) ^ (first.2 + 1 + (second.2 + 1))) scalar
  simp only [Finset.sum_mul, map_sum] at lifted
  change pairPolynomial data first second = _ at lifted
  rw [lifted]
  apply Finset.sum_congr rfl
  intro left hleft
  apply Finset.sum_congr rfl
  intro right hright
  have exponents : first.2 - left + (second.2 - right) + (left + 1 + (right + 1)) =
      first.2 + 1 + (second.2 + 1) := by
    have := Finset.mem_range.mp hleft
    have := Finset.mem_range.mp hright
    omega
  symm
  calc
    _ = MvPolynomial.C ((jetReflectionScalar first.2 left * jetReflectionScalar second.2 right) *
        pairScalar (left + 1) (right + 1) * (data.G first.1 second.1 : ℂ)) *
        ((MvPolynomial.X none : CorrectionPolynomial data) ^ (first.2 - left) *
          MvPolynomial.X none ^ (second.2 - right) *
          MvPolynomial.X none ^ (left + 1 + (right + 1))) := by
      simp only [reflectionFactor, pairPolynomial, sourceWeight, map_mul]
      ring
    _ = _ := by rw [← pow_add, ← pow_add, exponents]

private theorem pairDerivation_substitution_variable (index other : Index data) :
    pairDerivation data index (jetSubstitution (MvPolynomial.X (some other))) =
      ∑ reduced ∈ Finset.range (other.2 + 1),
        reflectionFactor other reduced * pairPolynomial data index (other.1, reduced) := by
  simp only [jetSubstitution, MvPolynomial.aeval_X, Option.elim_some, map_sum]
  apply Finset.sum_congr rfl
  intro reduced _
  simp [reflectionFactor, Derivation.leibniz, smul_eq_mul, pairDerivation_shift,
    pairDerivation, MvPolynomial.mkDerivation_X]

private theorem pairDerivation_substitution (index : Index data)
    (polynomial : CorrectionPolynomial data) :
    jetSubstitution (pairDerivation data index polynomial) =
      ∑ reduced ∈ Finset.range (index.2 + 1), reflectionFactor index reduced *
        pairDerivation data (index.1, reduced) (jetSubstitution polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp
  | add first second ihfirst ihsecond =>
    simp only [map_add, ihfirst, ihsecond, mul_add, Finset.sum_add_distrib]
  | mul_X polynomial coordinate ih =>
    have shift (other : Index data) : pairDerivation data other (MvPolynomial.X none) = 0 := by
      simpa using pairDerivation_shift data other 1
    cases coordinate with
    | none =>
      have variableLaw : jetSubstitution (MvPolynomial.X none) = MvPolynomial.X none := by
        simp [jetSubstitution]
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, shift,
        variableLaw, mul_zero, map_zero, zero_add, add_zero]
      rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro reduced _
      ring
    | some other =>
      have variableLaw (label : Index data) : pairDerivation data label
          (MvPolynomial.X (some other)) = pairPolynomial data label other := by
        simp [pairDerivation, MvPolynomial.mkDerivation_X]
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, variableLaw,
        substitution_pair]
      rw [ih, reflected_pair_lift index other]
      simp only [pairDerivation_substitution_variable, Finset.mul_sum, Finset.sum_mul,
        mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm]

private theorem singleton_reflection_lift (charge : Charge data) (index : Index data) :
    singletonPolynomial data charge index =
      (∑ reduced ∈ Finset.range (index.2 + 1), reflectionFactor index reduced *
        singletonPolynomial data charge (index.1, reduced)) +
      MvPolynomial.C ((-1 : ℂ) ^ (index.2 + 1) *
        (bilinear data (unitCharge data index.1) charge : ℂ)) *
          MvPolynomial.X none ^ (index.2 + 1) := by
  classical
  have lifted := congrArg (fun value : ℂ => MvPolynomial.C
    (value * (bilinear data (unitCharge data index.1) charge : ℂ)) *
      (MvPolynomial.X none : CorrectionPolynomial data) ^ (index.2 + 1))
        (singleton_correction_reflection index.2)
  simp only [add_mul, Finset.sum_mul, map_add, map_sum] at lifted
  unfold singletonPolynomial sourceWeight
  rw [lifted, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro reduced member
  have exponent : index.2 - reduced + (reduced + 1) = index.2 + 1 := by
    have := Finset.mem_range.mp member
    omega
  simp only [reflectionFactor, singletonPolynomial, sourceWeight, map_mul]
  rw [show (MvPolynomial.C (jetReflectionScalar index.2 reduced) *
      MvPolynomial.X none ^ (index.2 - reduced)) *
        (MvPolynomial.C (halfBinomial (reduced + 1)) *
          MvPolynomial.C (bilinear data (unitCharge data index.1) charge : ℂ) *
          MvPolynomial.X none ^ (reduced + 1)) =
      (MvPolynomial.C (jetReflectionScalar index.2 reduced) *
        MvPolynomial.C (halfBinomial (reduced + 1)) *
        MvPolynomial.C (bilinear data (unitCharge data index.1) charge : ℂ)) *
        (MvPolynomial.X none ^ (index.2 - reduced) *
          MvPolynomial.X none ^ (reduced + 1)) by ring, ← pow_add, exponent]

private theorem insertion_substitution (charge : Charge data) (index : Index data)
    (polynomial : CorrectionPolynomial data) :
    jetSubstitution (insertion data charge index polynomial) =
      (∑ reduced ∈ Finset.range (index.2 + 1), reflectionFactor index reduced *
        insertion data charge (index.1, reduced) (jetSubstitution polynomial)) +
      MvPolynomial.C ((-1 : ℂ) ^ (index.2 + 1) *
        (bilinear data (unitCharge data index.1) charge : ℂ)) *
          MvPolynomial.X none ^ (index.2 + 1) * jetSubstitution polynomial := by
  classical
  have singleton : jetSubstitution (singletonPolynomial data charge index) =
      singletonPolynomial data charge index := by
    simp [singletonPolynomial, jetSubstitution]
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, map_add, map_mul]
  rw [pairDerivation_substitution, singleton, singleton_reflection_lift charge index]
  simp only [jetSubstitution, MvPolynomial.aeval_X, Option.elim_some,
    add_mul, Finset.sum_mul]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  simp only [map_mul, mul_assoc, mul_left_comm, mul_comm]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm]
  ac_rfl

open LatticeHalfFockCurrentSeed LatticeHalfFockCurrentNormalRecurrence

private abbrev evaluation (charge : Charge data) := evaluateCorrection data determinantUnit charge

private def wordPolynomial (word : List (Index data)) : CorrectionPolynomial data :=
  (word.map (fun index => MvPolynomial.X (some index))).prod

private theorem evaluation_source_mul (charge : Charge data) (index : Index data)
    (polynomial : CorrectionPolynomial data) :
    evaluation charge (MvPolynomial.X (some index) * polynomial) =
      normalInsertionLinear data determinantUnit index (evaluation charge polynomial) := by
  change evaluatePolynomial data determinantUnit charge
    (MvPolynomial.optionEquivLeft ℂ (Index data) (MvPolynomial.X (some index) * polynomial)) = _
  rw [map_mul, MvPolynomial.optionEquivLeft_X_some, mul_comm, evaluate_source_mul]
  rfl

private theorem evaluation_word_shift (charge : Charge data) (word : List (Index data))
    (shift : ℕ) :
    evaluation charge (MvPolynomial.X none ^ shift * wordPolynomial word) =
      shiftLinear data determinantUnit shift (normalWord data determinantUnit charge word) := by
  classical
  induction word with
  | nil =>
    change evaluatePolynomial data determinantUnit charge
      (MvPolynomial.optionEquivLeft ℂ (Index data) (MvPolynomial.X none ^ shift * 1)) = _
    simp only [mul_one, map_pow, MvPolynomial.optionEquivLeft_X_none, normalWord]
    rw [← Polynomial.monomial_one_right_eq_X_pow, evaluate_monomial, normalPolynomial_one]
  | cons index tail ih =>
    simp only [wordPolynomial, List.map_cons, List.prod_cons] at *
    rw [show (MvPolynomial.X none : CorrectionPolynomial data) ^ shift *
        (MvPolynomial.X (some index) * (tail.map (fun i => MvPolynomial.X (some i))).prod) =
      MvPolynomial.X (some index) * (MvPolynomial.X none ^ shift *
        (tail.map (fun i => MvPolynomial.X (some i))).prod) by ring,
      evaluation_source_mul, ih, normalInsertion_shift]
    rfl

private theorem reduction_weight_le (word : List (Index data)) (choice : JetChoices word) :
    wordWeight data (reducedWord word choice) ≤ wordWeight data word := by
  induction word with
  | nil => rfl
  | cons index tail ih =>
    have := ih choice.2
    have := choice.1.isLt
    simp only [reducedWord, wordWeight, List.map_cons, List.sum_cons, sourceWeight] at *
    omega

private theorem substitution_word (word : List (Index data)) :
    jetSubstitution (wordPolynomial word) =
      ∑ choice : JetChoices word, MvPolynomial.C (reductionScalar word choice) *
        MvPolynomial.X none ^
          (wordWeight data word - wordWeight data (reducedWord word choice)) *
        wordPolynomial (reducedWord word choice) := by
  classical
  induction word with
  | nil => simp [wordPolynomial, reducedWord, reductionScalar, wordWeight, JetChoices]
  | cons index tail ih =>
    have variableLaw : jetSubstitution (MvPolynomial.X (some index)) =
        ∑ reduced : Fin (index.2 + 1), reflectionFactor index reduced.val *
          MvPolynomial.X (some (index.1, reduced.val)) := by
      simp only [jetSubstitution, MvPolynomial.aeval_X, Option.elim_some]
      exact (Fin.sum_univ_eq_sum_range (fun reduced : ℕ =>
        reflectionFactor index reduced * MvPolynomial.X (some (index.1, reduced)))
          (index.2 + 1)).symm
    change jetSubstitution (MvPolynomial.X (some index) * wordPolynomial tail) =
      ∑ choice : Fin (index.2 + 1) × JetChoices tail, _
    rw [map_mul, variableLaw, ih, Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro reduced _
    apply Finset.sum_congr rfl
    intro choice _
    have exponent : index.2 - reduced.val +
        (wordWeight data tail - wordWeight data (reducedWord tail choice)) =
        wordWeight data (index :: tail) -
          wordWeight data ((index.1, reduced.val) :: reducedWord tail choice) := by
      have := reduction_weight_le tail choice
      have := reduced.isLt
      simp only [wordWeight, List.map_cons, List.sum_cons, sourceWeight] at *
      omega
    simp only [reducedWord, reductionScalar, wordPolynomial, List.map_cons,
      List.prod_cons, reflectionFactor, map_mul]
    rw [show (MvPolynomial.C (jetReflectionScalar index.2 reduced.val) *
        MvPolynomial.X none ^ (index.2 - reduced.val) *
        MvPolynomial.X (some (index.1, reduced.val))) *
          (MvPolynomial.C (reductionScalar tail choice) *
            MvPolynomial.X none ^ (wordWeight data tail -
              wordWeight data (reducedWord tail choice)) *
            ((reducedWord tail choice).map (fun i => MvPolynomial.X (some i))).prod) =
      MvPolynomial.C (jetReflectionScalar index.2 reduced.val) *
        MvPolynomial.C (reductionScalar tail choice) *
          (MvPolynomial.X none ^ (index.2 - reduced.val) *
            MvPolynomial.X none ^ (wordWeight data tail -
              wordWeight data (reducedWord tail choice))) *
          (MvPolynomial.X (some (index.1, reduced.val)) *
            ((reducedWord tail choice).map (fun i => MvPolynomial.X (some i))).prod) by ring,
      ← pow_add, exponent]

private theorem flat_ground_reflection (charge : Charge data) (word : List (Index data))
    (modes : ModeTuple data word) (exponent : ℤ) (state : NativeTensor) :
    flatTerm data determinantUnit (chargedField data determinantUnit charge)
      word exponent (groundReflection charge state) modes =
    flatTerm data determinantUnit (oppositeChargedField charge) word exponent state modes := by
  induction word generalizing exponent state with
  | nil => rfl
  | cons index tail ih =>
    have commute : jetCurrent data determinantUnit index modes.1 (groundReflection charge state) =
        groundReflection charge (jetCurrent data determinantUnit index modes.1 state) := by
      simp only [jetCurrent, LinearMap.smul_apply, current_ground_reflection, map_smul]
    by_cases negative : modes.1 < 0
    · simp only [flatTerm, flatCoefficient, if_pos negative, Module.End.mul_apply]
      exact congrArg (jetCurrent data determinantUnit index modes.1) (ih modes.2 _ state)
    · simp only [flatTerm, flatCoefficient, if_neg negative, Module.End.mul_apply]
      rw [commute]
      exact ih modes.2 _ _

private theorem normal_word_ground_reflection (charge : Charge data)
    (word : List (Index data)) (exponent : ℤ) (state : NativeTensor) :
    (normalWord data determinantUnit charge word).coeff exponent (groundReflection charge state) =
      (normalSequence data determinantUnit (oppositeChargedField charge) word).coeff exponent state := by
  rw [normalWord_flattened, normalSequence_flattened]
  apply finsum_congr
  intro modes
  exact flat_ground_reflection charge word modes exponent state

private theorem evaluation_word_reflection (charge : Charge data) (word : List (Index data))
    (shift : ℕ) (exponent : ℤ) (first second : NativeTensor) :
    tensorPairing ((evaluation charge (MvPolynomial.X none ^ shift * wordPolynomial word)).coeff
      exponent first) second =
      tensorPairing first
        ((evaluation charge (jetSubstitution (MvPolynomial.X none ^ shift * wordPolynomial word))).coeff
          (-2 * chargeNorm data charge - exponent -
            4 * ((shift + wordWeight data word : ℕ) : ℤ)) (groundReflection charge second)) := by
  classical
  rw [evaluation_word_shift]
  change tensorPairing ((normalWord data determinantUnit charge word).coeff
    (exponent + 2 * shift) first) second = _
  rw [normal_word_source_reflection, map_mul, substitution_shift, substitution_word]
  simp only [Finset.mul_sum, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro choice _
  have weight := reduction_weight_le word choice
  have factor : (MvPolynomial.X none : CorrectionPolynomial data) ^ shift *
      (MvPolynomial.C (reductionScalar word choice) *
        MvPolynomial.X none ^ (wordWeight data word -
          wordWeight data (reducedWord word choice)) * wordPolynomial (reducedWord word choice)) =
      MvPolynomial.C (reductionScalar word choice) *
        MvPolynomial.X none ^ (shift + (wordWeight data word -
          wordWeight data (reducedWord word choice))) * wordPolynomial (reducedWord word choice) := by
    rw [pow_add]
    ring
  rw [factor, evaluate_shift_mul]
  have evaluationWord : evaluation charge (wordPolynomial (reducedWord word choice)) =
      normalWord data determinantUnit charge (reducedWord word choice) := by
    simpa only [pow_zero, one_mul, shiftLinear_zero] using
      evaluation_word_shift charge (reducedWord word choice) 0
  rw [evaluationWord]
  simp only [Pi.smul_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, shiftLinear, shiftField,
    LinearMap.coe_mk, AddHom.coe_mk, HVertexOperator.coeff_of_coeff]
  rw [normal_word_ground_reflection]
  have exponentLaw : -2 * chargeNorm data charge - exponent -
      4 * ((shift + wordWeight data word : ℕ) : ℤ) +
      2 * ((shift + (wordWeight data word - wordWeight data (reducedWord word choice)) : ℕ) : ℤ) =
      -2 * chargeNorm data charge - (exponent + 2 * shift) -
        2 * (wordWeight data word : ℤ) - 2 * (wordWeight data (reducedWord word choice) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub weight]
    omega
  rw [exponentLaw]

private theorem option_word (word : List (Index data)) :
    MvPolynomial.optionEquivLeft ℂ (Index data) (wordPolynomial word) =
      Polynomial.C ((word.map (fun index => (MvPolynomial.X index : Oscillator data))).prod) := by
  induction word with
  | nil => simp [wordPolynomial]
  | cons index tail ih =>
    simp only [wordPolynomial, List.map_cons, List.prod_cons, map_mul,
      MvPolynomial.optionEquivLeft_X_some] at *
    rw [ih, ← map_mul]

private theorem monomial_word_decomposition (exponent : Option (Index data) →₀ ℕ) (scalar : ℂ) :
    MvPolynomial.monomial exponent scalar = scalar •
      (MvPolynomial.X none ^ exponent none *
        wordPolynomial (LatticeAllStateField.occurrences data exponent.some)) := by
  apply (MvPolynomial.optionEquivLeft ℂ (Index data)).injective
  rw [MvPolynomial.optionEquivLeft_monomial, map_smul, map_mul, map_pow,
    MvPolynomial.optionEquivLeft_X_none, option_word, LatticeAllStateField.occurrences_product]
  rw [mul_comm (Polynomial.X ^ exponent none), Polynomial.C_mul_X_pow_eq_monomial]
  simp only [Polynomial.smul_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

private theorem weighted_evaluation_reflection (charge : Charge data)
    (polynomial : CorrectionPolynomial data) (weight : ℕ)
    (homogeneous : MvPolynomial.IsWeightedHomogeneous
      (LatticeHalfFockCorrectionGrading.correctionWeight data) polynomial weight)
    (exponent : ℤ) (first second : NativeTensor) :
    tensorPairing ((evaluation charge polynomial).coeff exponent first) second =
      tensorPairing first ((evaluation charge (jetSubstitution polynomial)).coeff
        (-2 * chargeNorm data charge - exponent - 4 * (weight : ℤ))
          (groundReflection charge second)) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum polynomial]
  conv_rhs => rw [MvPolynomial.as_sum polynomial]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro monomial member
  have weightLaw := homogeneous (MvPolynomial.mem_support_iff.mp member)
  have total : monomial none +
      wordWeight data (LatticeAllStateField.occurrences data monomial.some) = weight := by
    rw [LatticeHalfFockCorrectionGrading.wordWeight_occurrences]
    rw [← Finsupp.optionElim_some monomial, Finsupp.weight_apply,
      Finsupp.sum_option_index_smul] at weightLaw
    simpa only [Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
      LatticeHalfFockCorrectionGrading.correctionWeight, Option.elim_none,
      Option.elim_some, smul_eq_mul, mul_one, Finsupp.weight_apply] using weightLaw
  rw [monomial_word_decomposition]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [← total, evaluation_word_reflection]

private abbrev SourceChoices : List (Index data) → Type
  | [] => Unit
  | index :: tail => Option (Fin (index.2 + 1)) × SourceChoices tail

private instance sourceChoicesFintype (word : List (Index data)) : Fintype (SourceChoices word) := by
  induction word with
  | nil => exact inferInstanceAs (Fintype Unit)
  | cons index tail ih =>
    change Fintype (Option (Fin (index.2 + 1)) × SourceChoices tail)
    letI := ih
    infer_instance

private def reflectedSourceWord : (word : List (Index data)) → SourceChoices word → List (Index data)
  | [], _ => []
  | index :: tail, (none, choice) => reflectedSourceWord tail choice
  | index :: tail, (some reduced, choice) =>
      (index.1, reduced.val) :: reflectedSourceWord tail choice

private def sourceReflectionScalar (charge : Charge data) :
    (word : List (Index data)) → SourceChoices word → ℂ
  | [], _ => 1
  | index :: tail, (none, choice) =>
      ((-1 : ℂ) ^ (index.2 + 1) *
        (bilinear data (unitCharge data index.1) charge : ℂ)) *
          sourceReflectionScalar charge tail choice
  | index :: tail, (some reduced, choice) =>
      jetReflectionScalar index.2 reduced.val * sourceReflectionScalar charge tail choice

private theorem source_reflection_weight_le (word : List (Index data)) (choice : SourceChoices word) :
    wordWeight data (reflectedSourceWord word choice) ≤ wordWeight data word := by
  induction word with
  | nil => rfl
  | cons index tail ih =>
    rcases choice with ⟨head, choice⟩
    have := ih choice
    cases head with
    | none =>
      simp only [reflectedSourceWord, wordWeight, List.map_cons, List.sum_cons] at *
      omega
    | some reduced =>
      have := reduced.isLt
      simp only [reflectedSourceWord, wordWeight, List.map_cons, List.sum_cons, sourceWeight] at *
      omega

private theorem insertion_central (charge : Charge data) (index : Index data)
    (scalar : ℂ) (degree : ℕ) (polynomial : CorrectionPolynomial data) :
    insertion data charge index (MvPolynomial.C scalar * MvPolynomial.X none ^ degree * polynomial) =
      MvPolynomial.C scalar * MvPolynomial.X none ^ degree * insertion data charge index polynomial := by
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    Derivation.leibniz, smul_eq_mul, MvPolynomial.derivation_C, pairDerivation_shift,
    zero_mul, mul_zero, zero_add, add_zero]
  ring

private theorem corrected_word_substitution (charge : Charge data) (word : List (Index data)) :
    jetSubstitution (correctionWord data charge word) =
      ∑ choice : SourceChoices word, MvPolynomial.C (sourceReflectionScalar charge word choice) *
        MvPolynomial.X none ^
          (wordWeight data word - wordWeight data (reflectedSourceWord word choice)) *
        correctionWord data charge (reflectedSourceWord word choice) := by
  classical
  induction word with
  | nil => simp [correctionWord, SourceChoices, reflectedSourceWord, sourceReflectionScalar, wordWeight]
  | cons index tail ih =>
    have insertTail (reduced : ℕ) : insertion data charge (index.1, reduced)
        (jetSubstitution (correctionWord data charge tail)) =
        ∑ choice : SourceChoices tail, MvPolynomial.C (sourceReflectionScalar charge tail choice) *
          MvPolynomial.X none ^
            (wordWeight data tail - wordWeight data (reflectedSourceWord tail choice)) *
          correctionWord data charge ((index.1, reduced) :: reflectedSourceWord tail choice) := by
      rw [ih, map_sum]
      apply Finset.sum_congr rfl
      intro choice _
      exact insertion_central charge (index.1, reduced) _ _ _
    change jetSubstitution (insertion data charge index (correctionWord data charge tail)) =
      ∑ choice : Option (Fin (index.2 + 1)) × SourceChoices tail, _
    rw [insertion_substitution, Fintype.sum_prod_type, Fintype.sum_option]
    conv_lhs =>
      arg 1
      arg 2
      ext reduced
      rw [insertTail reduced]
    conv_lhs =>
      arg 2
      rw [ih]
    rw [add_comm]
    simp only [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro choice _
      have exponent : index.2 + 1 +
          (wordWeight data tail - wordWeight data (reflectedSourceWord tail choice)) =
          wordWeight data (index :: tail) - wordWeight data (reflectedSourceWord tail choice) := by
        have := source_reflection_weight_le tail choice
        simp only [wordWeight, List.map_cons, List.sum_cons, sourceWeight] at *
        omega
      simp only [reflectedSourceWord, sourceReflectionScalar, map_mul]
      rw [← exponent]
      simp only [pow_add]
      ring
    · rw [← Fin.sum_univ_eq_sum_range (fun reduced : ℕ =>
          ∑ choice : SourceChoices tail, reflectionFactor index reduced *
            (MvPolynomial.C (sourceReflectionScalar charge tail choice) *
              MvPolynomial.X none ^ (wordWeight data tail -
                wordWeight data (reflectedSourceWord tail choice)) *
              correctionWord data charge ((index.1, reduced) :: reflectedSourceWord tail choice)))
          (index.2 + 1)]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro reduced _
      apply Finset.sum_congr rfl
      intro choice _
      have exponent : index.2 - reduced.val +
          (wordWeight data tail - wordWeight data (reflectedSourceWord tail choice)) =
          wordWeight data (index :: tail) -
            wordWeight data ((index.1, reduced.val) :: reflectedSourceWord tail choice) := by
        have := source_reflection_weight_le tail choice
        have := reduced.isLt
        simp only [wordWeight, List.map_cons, List.sum_cons, sourceWeight] at *
        omega
      simp only [reflectionFactor, reflectedSourceWord, sourceReflectionScalar, map_mul]
      rw [show (MvPolynomial.C (jetReflectionScalar index.2 reduced.val) *
          MvPolynomial.X none ^ (index.2 - reduced.val)) *
            (MvPolynomial.C (sourceReflectionScalar charge tail choice) *
              MvPolynomial.X none ^ (wordWeight data tail -
                wordWeight data (reflectedSourceWord tail choice)) *
              correctionWord data charge ((index.1, reduced.val) :: reflectedSourceWord tail choice)) =
          MvPolynomial.C (jetReflectionScalar index.2 reduced.val) *
            MvPolynomial.C (sourceReflectionScalar charge tail choice) *
              (MvPolynomial.X none ^ (index.2 - reduced.val) *
                MvPolynomial.X none ^ (wordWeight data tail -
                  wordWeight data (reflectedSourceWord tail choice))) *
              correctionWord data charge ((index.1, reduced.val) :: reflectedSourceWord tail choice) by ring,
        ← pow_add, exponent]

private theorem corrected_word_source_reflection (charge : Charge data)
    (word : List (Index data)) (exponent : ℤ) (first second : NativeTensor) :
    tensorPairing ((correctedWord data determinantUnit charge word).coeff exponent first) second =
      ∑ choice : SourceChoices word, sourceReflectionScalar charge word choice * tensorPairing first
        ((correctedWord data determinantUnit charge (reflectedSourceWord word choice)).coeff
          (-2 * chargeNorm data charge - exponent - 2 * (wordWeight data word : ℤ) -
            2 * (wordWeight data (reflectedSourceWord word choice) : ℤ))
          (groundReflection charge second)) := by
  classical
  change tensorPairing ((evaluation charge (correctionWord data charge word)).coeff exponent first) second = _
  rw [weighted_evaluation_reflection charge _ _
    (LatticeHalfFockCorrectionGrading.correctionWord_weighted data charge word),
    corrected_word_substitution]
  simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro choice _
  rw [evaluate_shift_mul]
  simp only [Pi.smul_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, shiftLinear, shiftField,
    LinearMap.coe_mk, AddHom.coe_mk, HVertexOperator.coeff_of_coeff]
  have weight := source_reflection_weight_le word choice
  have exponentLaw : -2 * chargeNorm data charge - exponent -
      4 * (wordWeight data word : ℤ) +
      2 * ((wordWeight data word - wordWeight data (reflectedSourceWord word choice) : ℕ) : ℤ) =
      -2 * chargeNorm data charge - exponent - 2 * (wordWeight data word : ℤ) -
        2 * (wordWeight data (reflectedSourceWord word choice) : ℤ) := by
    rw [Nat.cast_sub weight]
    omega
  rw [exponentLaw]
  rfl

private theorem word_enumeration (word : List (Index data)) :
    word.Perm (LatticeAllStateField.occurrences data
      (Multiset.toFinsupp (word : Multiset (Index data)))) := by
  classical
  rw [LatticeAllStateField.occurrences, Multiset.toFinsupp_toMultiset]
  exact Multiset.coe_eq_coe.mp (Multiset.coe_toList (word : Multiset (Index data))).symm

private theorem original_word_field (charge : Charge data) (word : List (Index data)) :
    Ytw data determinantUnit
      (Finsupp.single charge ((word.map (fun index => (MvPolynomial.X index : Oscillator data))).prod)) =
        correctedWord data determinantUnit charge word := by
  classical
  have enumeration := word_enumeration word
  have product : (word.map (fun index => (MvPolynomial.X index : Oscillator data))).prod =
      MvPolynomial.monomial (Multiset.toFinsupp (word : Multiset (Index data))) 1 := by
    rw [← LatticeAllStateField.occurrences_product data]
    exact (enumeration.map _).prod_eq
  rw [product, Ytw_monomial_enumeration data determinantUnit charge _ word enumeration]

private theorem opposite_word_field (charge : Charge data) (word : List (Index data))
    (exponent : ℤ) (state : NativeTensor) :
    (nativeOppositeYtw (Finsupp.single charge
      ((word.map (fun index => (MvPolynomial.X index : Oscillator data))).prod))).coeff exponent state =
    (correctedWord data determinantUnit charge word).coeff exponent (groundReflection charge state) := by
  rw [← original_word_field]
  simp only [nativeOppositeYtw, Ytw, Finsupp.lsum_single]
  rfl

private theorem original_list_word_source_reflection (charge : Charge data)
    (word : List (Index data)) (exponent : ℤ) (first second : NativeTensor) :
    tensorPairing ((Ytw data determinantUnit (Finsupp.single charge
      ((word.map (fun index => (MvPolynomial.X index : Oscillator data))).prod))).coeff
        exponent first) second =
      ∑ choice : SourceChoices word, sourceReflectionScalar charge word choice * tensorPairing first
        ((nativeOppositeYtw (Finsupp.single charge
          (((reflectedSourceWord word choice).map
            (fun index => (MvPolynomial.X index : Oscillator data))).prod))).coeff
          (-2 * chargeNorm data charge - exponent - 2 * (wordWeight data word : ℤ) -
            2 * (wordWeight data (reflectedSourceWord word choice) : ℤ)) second) := by
  rw [original_word_field, corrected_word_source_reflection]
  apply Finset.sum_congr rfl
  intro choice _
  rw [opposite_word_field]


private theorem positional_source_sum (charge : Charge data) (count : ℕ)
    (entries : Fin count → Index data) (action : ℕ → Oscillator data →ₗ[ℂ] ℂ) :
    (∑ choice : SourceChoices (List.ofFn entries),
      sourceReflectionScalar charge (List.ofFn entries) choice *
        action (wordWeight data (reflectedSourceWord (List.ofFn entries) choice))
          (((reflectedSourceWord (List.ofFn entries) choice).map
            (fun index => (MvPolynomial.X index : Oscillator data))).prod)) =
    (-1 : ℂ) ^ (∑ j : Fin count, ((entries j).2 + 1)) *
      ∑ selection : ((j : Fin count) → Fin ((entries j).2 + 2)),
        (∏ j : Fin count, (((entries j).2 + 1).choose (selection j).val : ℂ)) *
          action (∑ j : Fin count, (selection j).val)
            (∏ j : Fin count, if (selection j).val = 0 then
              MvPolynomial.C (bilinear data (unitCharge data (entries j).1) charge : ℂ)
            else MvPolynomial.X ((entries j).1, (selection j).val - 1)) := by
  classical
  induction count generalizing action with
  | zero =>
    rw [List.ofFn_zero]
    simp [sourceReflectionScalar, reflectedSourceWord, wordWeight]
  | succ count ih =>
    rw [List.ofFn_succ, Fintype.sum_prod_type, Fintype.sum_option]
    conv_rhs =>
      arg 2
      rw [← (Fin.consEquiv (fun j : Fin (count + 1) =>
        Fin ((entries j).2 + 2))).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_succ]
    simp only [sourceReflectionScalar, reflectedSourceWord, List.map_cons, List.prod_cons,
      wordWeight, List.map_cons, List.sum_cons, sourceWeight]
    have ground := ih (fun j => entries j.succ) action
    have retained (reduced : Fin ((entries 0).2 + 1)) :=
      ih (fun j => entries j.succ)
        (fun weight => (action (reduced.val + 1 + weight)).comp
          (LinearMap.mulLeft ℂ (MvPolynomial.X ((entries 0).1, reduced.val))))
    simp only [wordWeight] at ground
    simp only [wordWeight, LinearMap.comp_apply, LinearMap.mulLeft_apply] at retained
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [ground]
    simp_rw [retained]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ,
      Fin.sum_univ_succ (M := ℕ), Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add, ite_true,
      Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, pow_add, jetReflectionScalar,
      mul_add, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro selection _
      simp only [← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      ring
    · apply Finset.sum_congr rfl
      intro reduced _
      apply Finset.sum_congr rfl
      intro selection _
      ring

theorem original_word_source_reflection (charge : Charge data) (count : ℕ)
    (axes : Fin count → Fin data.rank) (orders : Fin count → ℕ)
    (exponent : ℤ) (first second : NativeTensor) :
    let weight : ℕ := ∑ j : Fin count, (orders j + 1)
    tensorPairing ((Ytw data determinantUnit (Finsupp.single charge
      (∏ j : Fin count, MvPolynomial.X (axes j, orders j)))).coeff exponent first) second =
      (-1 : ℂ) ^ weight * ∑ selection : ((j : Fin count) → Fin (orders j + 2)),
        (∏ j : Fin count, ((orders j + 1).choose (selection j).val : ℂ)) *
        tensorPairing first ((nativeOppositeYtw (Finsupp.single charge
          (∏ j : Fin count, if (selection j).val = 0 then
            MvPolynomial.C (bilinear data (unitCharge data (axes j)) charge : ℂ)
          else MvPolynomial.X (axes j, (selection j).val - 1)))).coeff
          (-2 * chargeNorm data charge - exponent - 2 * (weight : ℤ) -
            2 * (∑ j : Fin count, ((selection j).val : ℤ))) second) := by
  classical
  dsimp only
  let entries : Fin count → Index data := fun j => (axes j, orders j)
  let action (weight : ℕ) : Oscillator data →ₗ[ℂ] ℂ := {
    toFun := fun polynomial => tensorPairing first
      ((nativeOppositeYtw (Finsupp.single charge polynomial)).coeff
        (-2 * chargeNorm data charge - exponent -
          2 * (wordWeight data (List.ofFn entries) : ℤ) - 2 * (weight : ℤ)) second)
    map_add' := by
      intro p q
      simp only [Finsupp.single_add, map_add, LinearMap.add_apply, Pi.add_apply]
    map_smul' := by
      intro c p
      simp only [← Finsupp.smul_single, map_smul, LinearMap.smul_apply,
        Pi.smul_apply, RingHom.id_apply] }
  have reflected := original_list_word_source_reflection charge (List.ofFn entries)
    exponent first second
  rw [show (∏ j : Fin count, MvPolynomial.X (axes j, orders j)) =
      ((List.ofFn entries).map (fun index =>
        (MvPolynomial.X index : Oscillator data))).prod by
        simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def, entries], reflected]
  change (∑ choice : SourceChoices (List.ofFn entries),
    sourceReflectionScalar charge (List.ofFn entries) choice *
      action (wordWeight data (reflectedSourceWord (List.ofFn entries) choice)) _) = _
  rw [positional_source_sum charge count entries action]
  simp only [action, LinearMap.coe_mk, AddHom.coe_mk, wordWeight,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, sourceWeight, entries, Nat.cast_sum]

#print axioms original_word_source_reflection
#print axioms original_list_word_source_reflection

#print axioms flat_word_source_reflection
#print axioms normal_word_source_reflection
#print axioms pairDerivation_substitution
#print axioms insertion_substitution

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockBpZ.original_jet_source_reflection
