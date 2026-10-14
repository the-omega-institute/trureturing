/- GID: D5/S3/VertexAlgebra/SuperFieldProducts
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/SuperFieldProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed formal-field products over an arbitrary complex module: integer-binomial residues, actual finite coefficient supports, Hasse derivatives and translation covariance. Exchange parameters remain explicit; no bc carrier or endpoint is assumed here. -/

import D5.S3.VertexAlgebra.FieldNormalProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.SuperFieldProducts

open FieldNormalProduct
open scoped VertexOperator

noncomputable section

variable {Space : Type*} [AddCommGroup Space] [Module ℂ Space]

def koszul (leftParity rightParity : ℕ) : ℂ := (-1) ^ (leftParity * rightParity)

def superCommutator (exchange : ℂ) (left right : VertexOperator ℂ Space) :
    ℤ → ℤ → Module.End ℂ Space :=
  fun first second => (left[[first]]) * (right[[second]]) -
    exchange • ((right[[second]]) * (left[[first]]))

def delta {Coefficient : Type*} [AddCommGroup Coefficient] (distribution : ℤ → ℤ → Coefficient) : ℤ → ℤ → Coefficient :=
  fun first second => distribution (first + 1) second - distribution first (second + 1)

def SuperLocal (leftParity rightParity : ℕ) (left right : VertexOperator ℂ Space) : Prop :=
  ∃ order : ℕ, delta^[order] (superCommutator (koszul leftParity rightParity) left right) = 0

theorem koszul_symm (leftParity rightParity : ℕ) :
    koszul leftParity rightParity = koszul rightParity leftParity := by
  simp [koszul, Nat.mul_comm]

theorem koszul_square (leftParity rightParity : ℕ) :
    koszul leftParity rightParity * koszul leftParity rightParity = 1 := by
  unfold koszul
  rw [← mul_pow]
  norm_num

theorem koszul_add_left (firstParity secondParity thirdParity : ℕ) :
    koszul (firstParity + secondParity) thirdParity =
      koszul firstParity thirdParity * koszul secondParity thirdParity := by
  simp [koszul, Nat.add_mul, pow_add]

theorem sign_power_mod (degree : ℕ) : (-1 : ℂ) ^ degree = (-1 : ℂ) ^ (degree % 2) := by
  nth_rewrite 1 [← Nat.mod_add_div degree 2]
  rw [pow_add, pow_mul]
  norm_num

theorem koszul_eq_of_mod (firstParity secondParity thirdParity fourthParity : ℕ)
    (leftGrade : firstParity % 2 = thirdParity % 2)
    (rightGrade : secondParity % 2 = fourthParity % 2) :
    koszul firstParity secondParity = koszul thirdParity fourthParity := by
  calc
    koszul firstParity secondParity = (-1 : ℂ) ^ ((firstParity * secondParity) % 2) :=
      sign_power_mod (firstParity * secondParity)
    _ = (-1 : ℂ) ^ ((thirdParity * fourthParity) % 2) := by
      rw [Nat.mul_mod, leftGrade, rightGrade, ← Nat.mul_mod]
    _ = koszul thirdParity fourthParity := (sign_power_mod (thirdParity * fourthParity)).symm

theorem superCommutator_add_left (exchange : ℂ) (first second third : VertexOperator ℂ Space) :
    superCommutator exchange (first + second) third =
      superCommutator exchange first third + superCommutator exchange second third := by
  funext left right
  simp only [superCommutator, map_add, Pi.add_apply, add_mul, mul_add, smul_add]
  abel

theorem superCommutator_add_right (exchange : ℂ) (first second third : VertexOperator ℂ Space) :
    superCommutator exchange first (second + third) =
      superCommutator exchange first second + superCommutator exchange first third := by
  funext left right
  simp only [superCommutator, map_add, Pi.add_apply, add_mul, mul_add, smul_add]
  abel

theorem superCommutator_smul_left (exchange scalar : ℂ) (first second : VertexOperator ℂ Space) :
    superCommutator exchange (scalar • first) second = scalar • superCommutator exchange first second := by
  funext left right
  simp only [superCommutator, map_smul, Pi.smul_apply, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm]
  module

theorem superCommutator_smul_right (exchange scalar : ℂ) (first second : VertexOperator ℂ Space) :
    superCommutator exchange first (scalar • second) = scalar • superCommutator exchange first second := by
  funext left right
  simp only [superCommutator, map_smul, Pi.smul_apply, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm]
  module

def integerBinomial (parameter : ℤ) (offset : ℕ) : ℂ :=
  ((Ring.choose parameter offset : ℤ) : ℂ)

def epsilon (parameter : ℤ) : ℂ := (-1) ^ parameter

def weight (parameter : ℤ) (offset : ℕ) : ℂ :=
  (-1) ^ offset * integerBinomial parameter offset

theorem increasing_finite (operator : VertexOperator ℂ Space) (start : ℤ) (vector : Space) :
    Function.HasFiniteSupport (fun offset : ℕ => (operator[[start + offset]]) vector) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (operator vector)).order - start).toNat, ?_⟩
  intro offset member
  contrapose! member
  rw [Function.notMem_support]
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  omega

theorem forward_finite (outer inner : VertexOperator ℂ Space) (start finish : ℤ) (vector : Space) :
    Function.HasFiniteSupport (fun offset : ℕ =>
      (outer[[start - offset]]) ((inner[[finish + offset]]) vector)) := by
  refine (increasing_finite inner finish vector).subset ?_
  intro offset member vanish
  apply member
  change (inner[[finish + offset]]) vector = 0 at vanish
  dsimp only
  rw [vanish, map_zero]

def residueLeft (parameter mode : ℤ) (left right : VertexOperator ℂ Space) (vector : Space) : Space :=
  ∑ᶠ offset : ℕ, weight parameter offset •
    (left[[parameter - offset]]) ((right[[mode + offset]]) vector)

def residueRight (parameter mode : ℤ) (left right : VertexOperator ℂ Space) (vector : Space) : Space :=
  ∑ᶠ offset : ℕ, weight parameter offset •
    (right[[parameter + mode - offset]]) ((left[[offset]]) vector)

theorem residue_left_finite (parameter mode : ℤ)
    (left right : VertexOperator ℂ Space) (vector : Space) :
    Function.HasFiniteSupport (fun offset : ℕ => weight parameter offset •
      (left[[parameter - offset]]) ((right[[mode + offset]]) vector)) :=
  (forward_finite left right parameter mode vector).smul_right (weight parameter)

theorem residue_right_finite (parameter mode : ℤ)
    (left right : VertexOperator ℂ Space) (vector : Space) :
    Function.HasFiniteSupport (fun offset : ℕ => weight parameter offset •
      (right[[parameter + mode - offset]]) ((left[[offset]]) vector)) := by
  simpa only [zero_add, Pi.smul_def'] using
    (forward_finite right left (parameter + mode) 0 vector).smul_right (weight parameter)

def residueCoefficient (exchange : ℂ) (parameter mode : ℤ)
    (left right : VertexOperator ℂ Space) : Module.End ℂ Space where
  toFun vector := residueLeft parameter mode left right vector -
    (epsilon parameter * exchange) • residueRight parameter mode left right vector
  map_add' first second := by
    dsimp [residueLeft, residueRight]
    simp only [map_add, smul_add]
    rw [finsum_add_distrib (residue_left_finite parameter mode left right first)
        (residue_left_finite parameter mode left right second),
      finsum_add_distrib (residue_right_finite parameter mode left right first)
        (residue_right_finite parameter mode left right second)]
    module
  map_smul' scalar vector := by
    dsimp [residueLeft, residueRight]
    simp only [map_smul]
    simp_rw [smul_comm (weight parameter _) scalar]
    rw [← smul_finsum' scalar (residue_left_finite parameter mode left right vector),
      ← smul_finsum' scalar (residue_right_finite parameter mode left right vector)]
    module

theorem residue_bounded (exchange : ℂ) (parameter : ℤ)
    (left right : VertexOperator ℂ Space) (vector : Space) :
    BddBelow (Function.support (fun power : ℤ =>
      residueCoefficient exchange parameter (-power - 1) left right vector)) := by
  classical
  let cutoff : ℕ := (-((HahnModule.of ℂ).symm (left vector)).order - 1).toNat
  let orders : Finset ℤ := (Finset.range (cutoff + 1)).image (fun offset : ℕ =>
    ((HahnModule.of ℂ).symm (right ((left[[offset]]) vector))).order + parameter - offset)
  let lower : ℤ := min ((HahnModule.of ℂ).symm (right vector)).order
    (orders.min' (by
      apply Finset.image_nonempty.mpr
      exact ⟨0, Finset.mem_range.mpr (by omega)⟩))
  refine ⟨lower, ?_⟩
  intro power member
  by_contra notLower
  have small : power < lower := lt_of_not_ge notLower
  have firstZero (offset : ℕ) :
      (left[[parameter - offset]]) ((right[[-power - 1 + offset]]) vector) = 0 := by
    have vanish : (right[[-power - 1 + offset]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      dsimp [lower] at small
      omega
    rw [vanish, map_zero]
  have secondZero (offset : ℕ) :
      (right[[parameter + (-power - 1) - offset]]) ((left[[offset]]) vector) = 0 := by
    by_cases within : offset ≤ cutoff
    · have inOrders : ((HahnModule.of ℂ).symm (right ((left[[offset]]) vector))).order +
          parameter - offset ∈ orders :=
        Finset.mem_image.mpr ⟨offset, Finset.mem_range.mpr (by omega), rfl⟩
      have bound := Finset.min'_le orders _ inOrders
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      dsimp [lower] at small
      omega
    · have vanish : (left[[offset]]) vector = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        dsimp [cutoff] at within
        omega
      rw [vanish, map_zero]
  exact member (by simp [residueCoefficient, residueLeft, residueRight, firstZero, secondZero])

def residue (exchange : ℂ) (parameter : ℤ) (left right : VertexOperator ℂ Space) :
    VertexOperator ℂ Space :=
  VertexOperator.of_coeff
    (fun power => residueCoefficient exchange parameter (-power - 1) left right)
    (residue_bounded exchange parameter left right)

theorem residue_modes (exchange : ℂ) (parameter mode : ℤ)
    (left right : VertexOperator ℂ Space) :
    ((residue exchange parameter left right)[[mode]]) =
      residueCoefficient exchange parameter mode left right := by
  rw [residue, VertexOperator.ncoeff_of_coeff]
  rw [show -(-mode - 1) - 1 = mode by omega]

def normal (exchange : ℂ) (left right : VertexOperator ℂ Space) : VertexOperator ℂ Space :=
  residue exchange (-1) left right

theorem weight_minus_one (offset : ℕ) : weight (-1) offset = 1 := by
  have negativeChoose : integerBinomial (-1) offset = (-1 : ℂ) ^ offset := by
    unfold integerBinomial
    rw [show (-1 : ℤ) = -((0 : ℤ) + 1) by omega, Ring.choose_neg,
      show (0 : ℤ) + 1 + offset - 1 = offset by omega, Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
      Int.cast_natCast, Nat.choose_self, Nat.cast_one, mul_one]
  rw [weight, negativeChoose, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem normal_modes (exchange : ℂ) (left right : VertexOperator ℂ Space)
    (mode : ℤ) (vector : Space) :
    ((normal exchange left right)[[mode]]) vector =
      (∑ᶠ offset : ℕ, (left[[-(offset : ℤ) - 1]]) ((right[[mode + offset]]) vector)) +
      exchange • (∑ᶠ offset : ℕ, (right[[mode - offset - 1]]) ((left[[offset]]) vector)) := by
  rw [normal, residue_modes]
  change residueLeft (-1) mode left right vector -
    (epsilon (-1) * exchange) • residueRight (-1) mode left right vector = _
  simp only [residueLeft, residueRight, weight_minus_one, one_smul]
  simp only [epsilon, show (-1 : ℂ) ^ (-1 : ℤ) = -1 by norm_num, neg_one_mul,
    neg_smul, sub_neg_eq_add,
    show ∀ offset : ℕ, (-1 : ℤ) - offset = -(offset : ℤ) - 1 by intro offset; omega,
    show ∀ offset : ℕ, (-1 : ℤ) + mode - offset = mode - offset - 1 by intro offset; omega]

theorem residue_vacuum (exchange : ℂ) (parameter : ℤ)
    (left right : VertexOperator ℂ Space) (vacuum : Space)
    (leftCreative : ∀ mode : ℤ, 0 ≤ mode → (left[[mode]]) vacuum = 0)
    (rightCreative : ∀ mode : ℤ, 0 ≤ mode → (right[[mode]]) vacuum = 0) :
    ((residue exchange parameter left right)[[-1]]) vacuum =
      (left[[parameter]]) ((right[[-1]]) vacuum) ∧
    ∀ mode : ℤ, 0 ≤ mode → ((residue exchange parameter left right)[[mode]]) vacuum = 0 := by
  have rightZero (mode : ℤ) : residueRight parameter mode left right vacuum = 0 := by
    unfold residueRight
    apply finsum_eq_zero_of_forall_eq_zero
    intro offset
    rw [leftCreative offset (by omega), map_zero, smul_zero]
  constructor
  · rw [residue_modes]
    change residueLeft parameter (-1) left right vacuum -
      (epsilon parameter * exchange) • residueRight parameter (-1) left right vacuum = _
    rw [rightZero, smul_zero, sub_zero]
    unfold residueLeft
    rw [finsum_eq_single _ 0]
    · simp [weight, integerBinomial]
    · intro offset distinct
      rw [rightCreative (-1 + (offset : ℤ)) (by omega), map_zero, smul_zero]
  · intro mode nonnegative
    rw [residue_modes]
    change residueLeft parameter mode left right vacuum -
      (epsilon parameter * exchange) • residueRight parameter mode left right vacuum = 0
    rw [rightZero, smul_zero, sub_zero]
    unfold residueLeft
    apply finsum_eq_zero_of_forall_eq_zero
    intro offset
    rw [rightCreative (mode + (offset : ℤ)) (by omega), map_zero, smul_zero]

theorem derivative_modes (degree : ℕ) (operator : VertexOperator ℂ Space) (mode : ℤ) :
    ((dividedDerivative degree operator)[[mode]]) =
      integerBinomial (-mode - 1 + degree) degree • (operator[[mode - degree]]) := by
  apply LinearMap.ext
  intro vector
  change Ring.choose (-mode - 1 + degree) degree •
    HVertexOperator.coeff operator (-mode - 1 + degree) vector = _
  rw [VertexOperator.coeff_eq_ncoeff,
    show -(-mode - 1 + degree) - 1 = mode - degree by omega]
  simp only [LinearMap.smul_apply, integerBinomial, Int.cast_smul_eq_zsmul]

theorem derivative_creative (degree : ℕ) (operator : VertexOperator ℂ Space) (vacuum : Space)
    (creative : ∀ mode : ℤ, 0 ≤ mode → (operator[[mode]]) vacuum = 0)
    (mode : ℤ) (nonnegative : 0 ≤ mode) :
    ((dividedDerivative degree operator)[[mode]]) vacuum = 0 := by
  rw [derivative_modes, LinearMap.smul_apply]
  by_cases within : (degree : ℤ) ≤ mode
  · rw [creative (mode - degree) (by omega), smul_zero]
  · have positive : 0 ≤ -mode - 1 + (degree : ℤ) := by omega
    obtain ⟨upper, equality⟩ := Int.eq_ofNat_of_zero_le positive
    have smaller : upper < degree := by omega
    simp [integerBinomial, equality, Ring.choose_natCast, Nat.choose_eq_zero_of_lt smaller]

theorem derivative_add (degree : ℕ) (first second : VertexOperator ℂ Space) :
    dividedDerivative degree (first + second) =
      dividedDerivative degree first + dividedDerivative degree second := by
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro vector
  simp only [VertexOperator.coeff_eq_ncoeff, derivative_modes, map_add, Pi.add_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_add]

theorem binomial_shift (parameter : ℤ) (degree : ℕ) :
    Ring.choose parameter degree * (parameter - degree) =
      parameter * Ring.choose (parameter - 1) degree := by
  have first := Ring.choose_smul_choose parameter (n := degree + 1) (k := degree) (by omega)
  have second := Ring.choose_smul_choose parameter (n := degree + 1) (k := 1) (by omega)
  rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right] at first
  rw [Nat.choose_one_right, Ring.choose_one_right, Nat.add_sub_cancel] at second
  exact first.symm.trans second

theorem derivative_translation (translation : Module.End ℂ Space)
    (operator : VertexOperator ℂ Space)
    (covariant : ∀ mode : ℤ, translation * (operator[[mode]]) - (operator[[mode]]) * translation =
      -(mode : ℂ) • (operator[[mode - 1]])) (degree : ℕ) (mode : ℤ) :
    translation * ((dividedDerivative degree operator)[[mode]]) -
      ((dividedDerivative degree operator)[[mode]]) * translation =
        -(mode : ℂ) • ((dividedDerivative degree operator)[[mode - 1]]) := by
  rw [derivative_modes, derivative_modes, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    ← smul_sub, covariant, smul_smul]
  rw [show mode - (degree : ℤ) - 1 = mode - 1 - degree by omega, smul_smul]
  have identity := congrArg (fun scalar : ℤ => (scalar : ℂ))
    (binomial_shift (-mode + degree) degree)
  push_cast at identity
  rw [show -mode + (degree : ℤ) - 1 = -mode - 1 + degree by omega] at identity
  rw [show -(mode - 1) - 1 + (degree : ℤ) = -mode + degree by omega]
  congr 1
  dsimp [integerBinomial]
  push_cast
  linear_combination -identity

theorem residue_translation (exchange : ℂ) (parameter : ℤ)
    (translation : Module.End ℂ Space) (left right : VertexOperator ℂ Space)
    (leftLaw : ∀ mode : ℤ, translation * (left[[mode]]) - (left[[mode]]) * translation =
      -(mode : ℂ) • (left[[mode - 1]]))
    (rightLaw : ∀ mode : ℤ, translation * (right[[mode]]) - (right[[mode]]) * translation =
      -(mode : ℂ) • (right[[mode - 1]])) (mode : ℤ) :
    translation * ((residue exchange parameter left right)[[mode]]) -
      ((residue exchange parameter left right)[[mode]]) * translation =
        -(mode : ℂ) • ((residue exchange parameter left right)[[mode - 1]]) := by
  have relation (offset : ℕ) : weight parameter (offset + 1) * ((offset : ℂ) + 1) =
      -(weight parameter offset * ((parameter : ℂ) - offset)) := by
    have raw := Ring.choose_smul_choose parameter (n := offset + 1) (k := offset)
      (Nat.le_succ offset)
    simp only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
      Ring.choose_one_right, nsmul_eq_mul] at raw
    have cast : ((offset : ℂ) + 1) * integerBinomial parameter (offset + 1) =
        integerBinomial parameter offset * ((parameter : ℂ) - offset) := by
      dsimp [integerBinomial]
      exact_mod_cast raw
    dsimp [weight]
    rw [pow_succ]
    calc
      _ = -((-1 : ℂ) ^ offset *
          (((offset : ℂ) + 1) * integerBinomial parameter (offset + 1))) := by ring
      _ = _ := by rw [cast]; ring
  let zeroSucc : Option ℕ ≃ ℕ := {
    toFun value := match value with | none => 0 | some offset => offset + 1
    invFun value := match value with | 0 => none | offset + 1 => some offset
    left_inv value := by cases value <;> rfl
    right_inv value := by cases value <;> rfl }
  have shiftSum (term : ℕ → Space) (finite : Function.HasFiniteSupport term) (atZero : term 0 = 0) :
      (∑ᶠ offset : ℕ, term offset) = ∑ᶠ offset : ℕ, term (offset + 1) := by
    rw [← finsum_comp_equiv zeroSucc, finsum_option]
    · simp [zeroSucc, atZero]
    · exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1)
        (fun first second equality => Nat.add_right_cancel equality)
  have telescope (sequence : ℤ → Space)
      (finite : Function.HasFiniteSupport (fun offset : ℕ => sequence offset))
      (shiftedFinite : Function.HasFiniteSupport (fun offset : ℕ => sequence ((offset : ℤ) - 1))) :
      Function.HasFiniteSupport (fun offset : ℕ => weight parameter offset •
        (((parameter : ℂ) - offset) • sequence offset +
          (offset : ℂ) • sequence ((offset : ℤ) - 1))) ∧
      (∑ᶠ offset : ℕ, weight parameter offset •
        (((parameter : ℂ) - offset) • sequence offset +
          (offset : ℂ) • sequence ((offset : ℤ) - 1))) = 0 := by
    have firstFinite := finite.smul_right
      (fun offset => weight parameter offset * ((parameter : ℂ) - offset))
    have secondFinite := shiftedFinite.smul_right
      (fun offset => weight parameter offset * (offset : ℂ))
    simp only [Pi.smul_def'] at firstFinite secondFinite
    constructor
    · simpa only [Pi.add_def, smul_add, smul_smul]
        using firstFinite.add secondFinite
    · simp only [smul_add, smul_smul]
      rw [finsum_add_distrib firstFinite secondFinite,
        shiftSum _ secondFinite (by simp)]
      have shifted (offset : ℕ) :
          (weight parameter (offset + 1) * ((offset + 1 : ℕ) : ℂ)) •
            sequence (((offset + 1 : ℕ) : ℤ) - 1) =
              -((weight parameter offset * ((parameter : ℂ) - offset)) • sequence offset) := by
        rw [Nat.cast_add, Nat.cast_one, relation,
          show ((offset + 1 : ℕ) : ℤ) - 1 = offset by omega, neg_smul]
      simp_rw [shifted]
      rw [finsum_neg_distrib]
      abel
  let weightedSum (outer inner : VertexOperator ℂ Space) (start finish : ℤ) (vector : Space) : Space :=
    ∑ᶠ offset : ℕ, weight parameter offset •
      (outer[[start - offset]]) ((inner[[finish + offset]]) vector)
  have branchLaw (outer inner : VertexOperator ℂ Space)
      (outerLaw : ∀ index : ℤ, translation * (outer[[index]]) - (outer[[index]]) * translation =
        -(index : ℂ) • (outer[[index - 1]]))
      (innerLaw : ∀ index : ℤ, translation * (inner[[index]]) - (inner[[index]]) * translation =
        -(index : ℂ) • (inner[[index - 1]])) (start finish : ℤ) (vector : Space) :
      translation (weightedSum outer inner start finish vector) -
        weightedSum outer inner start finish (translation vector) =
          -((start : ℂ) - parameter) • weightedSum outer inner (start - 1) finish vector -
            (finish : ℂ) • weightedSum outer inner start (finish - 1) vector := by
    let sequence (index : ℤ) : Space :=
      (outer[[start - index - 1]]) ((inner[[finish + index]]) vector)
    have sequenceFinite : Function.HasFiniteSupport (fun offset : ℕ => sequence offset) := by
      simpa only [sequence, sub_right_comm] using
        forward_finite outer inner (start - 1) finish vector
    have sequenceShifted : Function.HasFiniteSupport
        (fun offset : ℕ => sequence ((offset : ℤ) - 1)) := by
      have arithmetic (offset : ℕ) : start - ((offset : ℤ) - 1) - 1 = start - offset := by omega
      simpa only [sequence, arithmetic, add_sub_assoc, sub_add_eq_add_sub] using
        forward_finite outer inner start (finish - 1) vector
    have cancellation := telescope sequence sequenceFinite sequenceShifted
    let terms (offset : ℕ) : Module.End ℂ Space :=
      weight parameter offset • ((outer[[start - offset]]) * (inner[[finish + offset]]))
    have finiteTerms (input : Space) : Function.HasFiniteSupport (fun offset => terms offset input) :=
      (forward_finite outer inner start finish input).smul_right (weight parameter)
    have commuteSum : translation (∑ᶠ offset : ℕ, terms offset vector) -
        (∑ᶠ offset : ℕ, terms offset (translation vector)) =
          ∑ᶠ offset : ℕ, (translation * terms offset - terms offset * translation) vector := by
      rw [map_finsum translation (finiteTerms vector),
        ← finsum_sub_distrib ((finiteTerms vector).fun_comp (map_zero translation))
          (finiteTerms (translation vector))]
      rfl
    have productLaw (first second : ℤ) :
        translation * ((outer[[first]]) * (inner[[second]])) -
          ((outer[[first]]) * (inner[[second]])) * translation =
            -(first : ℂ) • ((outer[[first - 1]]) * (inner[[second]])) +
              -(second : ℂ) • ((outer[[first]]) * (inner[[second - 1]])) := by
      calc
        _ = (translation * (outer[[first]]) - (outer[[first]]) * translation) * (inner[[second]]) +
            (outer[[first]]) * (translation * (inner[[second]]) - (inner[[second]]) * translation) := by
              noncomm_ring
        _ = _ := by rw [outerLaw, innerLaw]; simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    have pointwise (offset : ℕ) :
        (translation * terms offset - terms offset * translation) vector =
          (-((start : ℂ) - parameter) • (weight parameter offset • sequence offset) -
            (finish : ℂ) • (weight parameter offset • sequence ((offset : ℤ) - 1))) -
          weight parameter offset • (((parameter : ℂ) - offset) • sequence offset +
            (offset : ℂ) • sequence ((offset : ℤ) - 1)) := by
      dsimp only [terms]
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub, productLaw]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply]
      dsimp only [sequence]
      rw [show start - ((offset : ℤ) - 1) - 1 = start - offset by omega,
        show finish + ((offset : ℤ) - 1) = finish + offset - 1 by omega]
      push_cast
      module
    change translation (∑ᶠ offset : ℕ, terms offset vector) -
      (∑ᶠ offset : ℕ, terms offset (translation vector)) = _
    rw [commuteSum]
    simp_rw [pointwise]
    have firstFinite := (sequenceFinite.smul_right (weight parameter)).smul_right
      (fun _ => -((start : ℂ) - parameter))
    have secondFinite := (sequenceShifted.smul_right (weight parameter)).smul_right
      (fun _ => (finish : ℂ))
    simp only [Pi.smul_def'] at firstFinite secondFinite
    have mainFinite := firstFinite.sub secondFinite
    have sequenceWeighted := sequenceFinite.smul_right (weight parameter)
    have shiftedWeighted := sequenceShifted.smul_right (weight parameter)
    simp only [Pi.smul_def', Pi.sub_def] at mainFinite sequenceWeighted shiftedWeighted
    rw [finsum_sub_distrib mainFinite cancellation.1, cancellation.2, sub_zero,
      finsum_sub_distrib firstFinite secondFinite, ← smul_finsum' _ sequenceWeighted,
      ← smul_finsum' _ shiftedWeighted]
    congr 1
    · dsimp [weightedSum, sequence]
      apply congrArg (fun value : Space => -((start : ℂ) - parameter) • value)
      apply finsum_congr
      intro offset
      rw [show start - (offset : ℤ) - 1 = start - 1 - offset by omega]
    · dsimp [weightedSum, sequence]
      apply congrArg (fun value : Space => (finish : ℂ) • value)
      apply finsum_congr
      intro offset
      rw [show start - ((offset : ℤ) - 1) - 1 = start - offset by omega,
        show finish + ((offset : ℤ) - 1) = finish - 1 + offset by omega]
  have firstMatch (index : ℤ) (input : Space) : residueLeft parameter index left right input =
      weightedSum left right parameter index input := rfl
  have secondMatch (index : ℤ) (input : Space) : residueRight parameter index left right input =
      weightedSum right left (parameter + index) 0 input := by
    dsimp only [residueRight, weightedSum]
    simp only [zero_add]
  apply LinearMap.ext
  intro vector
  change translation (((residue exchange parameter left right)[[mode]]) vector) -
    ((residue exchange parameter left right)[[mode]]) (translation vector) = _
  simp only [residue_modes]
  change translation (residueLeft parameter mode left right vector -
      (epsilon parameter * exchange) • residueRight parameter mode left right vector) -
    (residueLeft parameter mode left right (translation vector) -
      (epsilon parameter * exchange) • residueRight parameter mode left right (translation vector)) =
    -(mode : ℂ) • (residueLeft parameter (mode - 1) left right vector -
      (epsilon parameter * exchange) • residueRight parameter (mode - 1) left right vector)
  have firstLaw := branchLaw left right leftLaw rightLaw parameter mode vector
  have secondLaw := branchLaw right left rightLaw leftLaw (parameter + mode) 0 vector
  simp only [sub_self, Int.cast_add, add_sub_cancel_left] at firstLaw secondLaw
  simp only [firstMatch, secondMatch]
  rw [map_sub, map_smul]
  rw [show parameter + mode - 1 = parameter + (mode - 1) by omega] at secondLaw
  calc
    _ = (translation (weightedSum left right parameter mode vector) -
          weightedSum left right parameter mode (translation vector)) -
        (epsilon parameter * exchange) •
          (translation (weightedSum right left (parameter + mode) 0 vector) -
            weightedSum right left (parameter + mode) 0 (translation vector)) := by module
    _ = _ := by rw [firstLaw, secondLaw]; module

theorem negative_residue_normal (exchange : ℂ) (degree : ℕ)
    (left right : VertexOperator ℂ Space) :
    residue exchange (-(degree : ℤ) - 1) left right =
      normal exchange (dividedDerivative degree left) right := by
  have square (offset : ℕ) : (-1 : ℂ) ^ offset * (-1 : ℂ) ^ offset = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have negativeChoose (offset : ℕ) :
      integerBinomial (-(degree : ℤ) - 1) offset =
        (-1 : ℂ) ^ offset * ((degree + offset).choose degree : ℂ) := by
    unfold integerBinomial
    rw [show -(degree : ℤ) - 1 = -((degree : ℤ) + 1) by omega,
      Ring.choose_neg,
      show (degree : ℤ) + 1 + offset - 1 = ((degree + offset : ℕ) : ℤ) by omega,
      Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
      Int.cast_natCast]
    rw [← Nat.choose_symm_add]
  have negativeWeight (offset : ℕ) : weight (-(degree : ℤ) - 1) offset =
      ((degree + offset).choose degree : ℂ) := by
    rw [weight, negativeChoose, ← mul_assoc, square, one_mul]
  have sign : -epsilon (-(degree : ℤ) - 1) = (-1 : ℂ) ^ degree := by
    rw [epsilon, show -(degree : ℤ) - 1 = -((degree + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, ← inv_pow]
    norm_num [pow_succ]
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro vector
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    residue_modes, normal_modes]
  let mode : ℤ := -power - 1
  have forwardEquality : residueLeft (-(degree : ℤ) - 1) mode left right vector =
      ∑ᶠ offset : ℕ, ((dividedDerivative degree left)[[-(offset : ℤ) - 1]])
        ((right[[mode + offset]]) vector) := by
    unfold residueLeft
    apply finsum_congr
    intro offset
    rw [negativeWeight, derivative_modes, LinearMap.smul_apply]
    have parameter : -(-(offset : ℤ) - 1) - 1 + degree = ((degree + offset : ℕ) : ℤ) := by omega
    rw [parameter]
    simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast]
    rw [show -(degree : ℤ) - 1 - offset = -(offset : ℤ) - 1 - degree by omega]
  let term (offset : ℕ) : Space := (right[[mode - offset - 1]])
    (((dividedDerivative degree left)[[offset]]) vector)
  have initialZero (offset : Fin degree) : term offset = 0 := by
    have parameter : -(offset : ℤ) - 1 + degree = ((degree - offset - 1 : ℕ) : ℤ) := by omega
    have zeroChoose : integerBinomial (-(offset : ℤ) - 1 + degree) degree = 0 := by
      rw [parameter, integerBinomial, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    simp [term, derivative_modes, zeroChoose]
  have split : (∑ᶠ offset : ℕ, term offset) = ∑ᶠ offset : ℕ, term (degree + offset) := by
    have subset : Function.support term ⊆ Set.range (fun offset : ℕ => degree + offset) := by
      intro offset member
      have bound : degree ≤ offset := by
        by_contra smaller
        exact member (initialZero ⟨offset, by omega⟩)
      exact ⟨offset - degree, by change degree + (offset - degree) = offset; omega⟩
    have sets : Set.range (fun offset : ℕ => degree + offset) ∩ Function.support term =
        Set.univ ∩ Function.support term := by
      rw [Set.inter_eq_right.mpr subset, Set.univ_inter]
    rw [← finsum_mem_range (f := term) (g := fun offset : ℕ => degree + offset)
      (fun first second equality => Nat.add_left_cancel equality),
      finsum_mem_inter_support_eq term _ _ sets, finsum_mem_univ]
  have reverseEquality : (∑ᶠ offset : ℕ, term offset) =
      (-1 : ℂ) ^ degree • residueRight (-(degree : ℤ) - 1) mode left right vector := by
    rw [split, residueRight, smul_finsum' _
      (residue_right_finite (-(degree : ℤ) - 1) mode left right vector)]
    apply finsum_congr
    intro offset
    dsimp [term]
    rw [derivative_modes, LinearMap.smul_apply, map_smul, negativeWeight]
    rw [show -((degree : ℤ) + offset) - 1 + degree = -(offset : ℤ) - 1 by omega,
      integerBinomial,
      show -(offset : ℤ) - 1 = -((offset : ℤ) + 1) by omega,
      Ring.choose_neg,
      show (offset : ℤ) + 1 + degree - 1 = ((degree + offset : ℕ) : ℤ) by omega,
      Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
      Int.cast_natCast, smul_smul]
    rw [show (degree : ℤ) + offset - degree = offset by omega,
      show mode - ((degree : ℤ) + offset) - 1 = -(degree : ℤ) - 1 + mode - offset by omega]
  change residueLeft (-(degree : ℤ) - 1) mode left right vector -
    (epsilon (-(degree : ℤ) - 1) * exchange) • residueRight (-(degree : ℤ) - 1) mode left right vector =
    _ + exchange • ∑ᶠ offset : ℕ, term offset
  rw [forwardEquality, reverseEquality, sub_eq_add_neg, ← neg_smul, ← neg_mul, sign]
  simp only [smul_smul, mul_comm exchange]
  rfl

end
end D5.S3.VertexAlgebra.SuperFieldProducts
