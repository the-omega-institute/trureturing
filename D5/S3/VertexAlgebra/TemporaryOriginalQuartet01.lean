import D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber
import D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
  LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def gramPair (D : LatticeData) (left right : Fin D.rank → ℂ) : ℂ :=
  ∑ first, ∑ second, left first * (D.G first second : ℂ) * right second

def directionalCurrent (D : LatticeData) (direction : Fin D.rank → ℂ)
    (mode : ℤ) : Module.End ℂ (Carrier D) :=
  ∑ index, direction index • neutralMode D index mode

def O (D : LatticeData) (direction : Fin D.rank → ℂ) (mode : ℤ) :
    Module.End ℂ (State D) :=
  TensorProduct.map (directionalCurrent D direction mode) LinearMap.id

theorem gramPair_symm (D : LatticeData) (left right : Fin D.rank → ℂ) :
    gramPair D left right = gramPair D right left := by
  classical
  unfold gramPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first firstMember
  apply Finset.sum_congr rfl
  intro second secondMember
  rw [D.symmetric second first]
  ring

theorem directionalCurrent_heisenberg (D : LatticeData)
    (left right : Fin D.rank → ℂ) (firstMode secondMode : ℤ) :
    directionalCurrent D left firstMode * directionalCurrent D right secondMode -
      directionalCurrent D right secondMode * directionalCurrent D left firstMode =
      (if firstMode + secondMode = 0 then
        (firstMode : ℂ) * gramPair D left right else 0) •
        (1 : Module.End ℂ (Carrier D)) := by
  classical
  have productExpansion (firstDirection secondDirection : Fin D.rank → ℂ)
      (first second : ℤ) :
      directionalCurrent D firstDirection first * directionalCurrent D secondDirection second =
        ∑ firstIndex, ∑ secondIndex, (firstDirection firstIndex * secondDirection secondIndex) •
          (neutralMode D firstIndex first * neutralMode D secondIndex second) := by
    unfold directionalCurrent
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro firstIndex firstMember
    apply Finset.sum_congr rfl
    intro secondIndex secondMember
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have reverseExpansion :
      directionalCurrent D right secondMode * directionalCurrent D left firstMode =
        ∑ first, ∑ second, (left first * right second) •
          (neutralMode D second secondMode * neutralMode D first firstMode) := by
    rw [productExpansion, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first firstMember
    apply Finset.sum_congr rfl
    intro second secondMember
    rw [mul_comm (right second) (left first)]
  have expansion :
      directionalCurrent D left firstMode * directionalCurrent D right secondMode -
        directionalCurrent D right secondMode * directionalCurrent D left firstMode =
      ∑ first, ∑ second, (left first * right second) •
        (neutralMode D first firstMode * neutralMode D second secondMode -
          neutralMode D second secondMode * neutralMode D first firstMode) := by
    rw [productExpansion, reverseExpansion]
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [expansion]
  simp_rw [neutralMode_heisenberg]
  by_cases resonant : firstMode + secondMode = 0
  · simp only [if_pos resonant, smul_smul]
    simp only [gramPair, Finset.mul_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro first firstMember
    apply Finset.sum_congr rfl
    intro second secondMember
    congr 1
    ring
  · simp [resonant]

theorem O_heisenberg (D : LatticeData) (left right : Fin D.rank → ℂ)
    (firstMode secondMode : ℤ) :
    O D left firstMode * O D right secondMode -
      O D right secondMode * O D left firstMode =
      (if firstMode + secondMode = 0 then
        (firstMode : ℂ) * gramPair D left right else 0) •
        (1 : Module.End ℂ (State D)) := by
  have lifted := congrArg (LinearMap.rTensorHom (Fock ℂ))
    (directionalCurrent_heisenberg D left right firstMode secondMode)
  simp only [map_sub, map_smul, LinearMap.coe_rTensorHom,
    LinearMap.rTensor_mul, Module.End.one_eq_id, LinearMap.rTensor_id] at lifted
  simpa only [O, LinearMap.rTensor_def, Module.End.one_eq_id] using lifted

theorem O_C_commute (D : LatticeData) (direction : Fin D.rank → ℂ)
    (matterMode ghostMode : ℤ) :
    O D direction matterMode * C D ghostMode = C D ghostMode * O D direction matterMode := by
  apply TensorProduct.ext'
  intro matter ghost
  simp [O, C, Module.End.mul_apply]

theorem O_B_commute (D : LatticeData) (direction : Fin D.rank → ℂ)
    (matterMode ghostMode : ℤ) :
    O D direction matterMode * B D ghostMode = B D ghostMode * O D direction matterMode := by
  apply TensorProduct.ext'
  intro matter ghost
  simp [O, B, Module.End.mul_apply]

theorem C_C_anticommute (D : LatticeData) (first second : ℤ) :
    C D first * C D second + C D second * C D first = 0 := by
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostStressCurrent.c_c (K := ℂ) first second)
  simp only [map_add, map_zero, LinearMap.coe_lTensorHom,
    LinearMap.lTensor_mul] at lifted
  simpa only [C, LinearMap.lTensor_def] using lifted

theorem B_B_anticommute (D : LatticeData) (first second : ℤ) :
    B D first * B D second + B D second * B D first = 0 := by
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostStressCurrent.b_b (K := ℂ) first second)
  simp only [map_add, map_zero, LinearMap.coe_lTensorHom,
    LinearMap.lTensor_mul] at lifted
  simpa only [B, LinearMap.lTensor_def] using lifted

theorem C_B_anticommute (D : LatticeData) (first second : ℤ) :
    C D first * B D second + B D second * C D first =
      if second + first = 0 then 1 else 0 := by
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostStressCurrent.b_c (K := ℂ) second first)
  by_cases resonant : second + first = 0
  · simp only [resonant, if_true, map_add, LinearMap.coe_lTensorHom,
      LinearMap.lTensor_mul, Module.End.one_eq_id, LinearMap.lTensor_id] at lifted
    simpa only [B, C, resonant, if_true, Module.End.one_eq_id,
      LinearMap.lTensor_def, add_comm] using lifted
  · have reverseNonresonant : first + second ≠ 0 := by omega
    simp only [resonant, if_false, map_add, map_zero, LinearMap.coe_lTensorHom,
      LinearMap.lTensor_mul] at lifted
    simpa only [B, C, resonant, reverseNonresonant, if_false, LinearMap.lTensor_def, add_comm] using lifted

theorem directionalCurrent_high (D : LatticeData) (direction : Fin D.rank → ℂ)
    (matter : Carrier D) (mode : ℤ)
    (above : (vectorFrequencyBound D matter : ℤ) < mode) :
    directionalCurrent D direction mode matter = 0 := by
  classical
  have currentZero (index : Fin D.rank) : neutralMode D index mode matter = 0 :=
    neutralMode_vanish D index matter mode above
  simp [directionalCurrent, currentZero]

theorem c_high (ghost : Fock ℂ) (mode : ℤ)
    (above : (((occupied ghost).sup id : ℕ) : ℤ) + 4 < mode) : c mode ghost = 0 := by
  have branch : ¬ mode ≤ 1 := by omega
  have indexAbove : (occupied ghost).sup id < 2 * (mode - 2).toNat := by
    omega
  simp [c, branch, annihilate_eq_zero_of_sup_lt ghost _ indexAbove]

theorem b_high (ghost : Fock ℂ) (mode : ℤ)
    (above : (((occupied ghost).sup id : ℕ) : ℤ) + 4 < mode) : b mode ghost = 0 := by
  have branch : ¬ mode ≤ -2 := by omega
  have indexAbove : (occupied ghost).sup id < 2 * (mode + 1).toNat + 1 := by
    omega
  simp [b, branch, annihilate_eq_zero_of_sup_lt ghost _ indexAbove]

def dAtom (D : LatticeData) (longitudinal : Fin D.rank → ℂ) (mode : ℤ) :
    Module.End ℂ (State D) :=
  if mode = 0 then 0 else C D (-mode) * O D longitudinal mode

def rAtom (D : LatticeData) (nullDirection : Fin D.rank → ℂ) (mode : ℤ) :
    Module.End ℂ (State D) :=
  if mode = 0 then 0 else
    ((mode.natAbs : ℂ)⁻¹) • (O D nullDirection (-mode) * B D mode)

theorem dAtom_finite (D : LatticeData) (longitudinal : Fin D.rank → ℂ)
    (state : State D) :
    Function.HasFiniteSupport (fun mode : ℤ => dAtom D longitudinal mode state) := by
  induction state using TensorProduct.induction_on with
  | zero => simp [Function.HasFiniteSupport]
  | tmul matter ghost =>
      apply (Set.finite_Icc (-(((occupied ghost).sup id : ℕ) : ℤ) - 4)
        (vectorFrequencyBound D matter : ℤ)).subset
      intro mode nonzero
      have zeroOutside (outside :
          mode < -(((occupied ghost).sup id : ℕ) : ℤ) - 4 ∨
            (vectorFrequencyBound D matter : ℤ) < mode) :
          dAtom D longitudinal mode (matter ⊗ₜ[ℂ] ghost) = 0 := by
        rcases outside with below | above
        · have ghostZero := c_high ghost (-mode) (by omega)
          by_cases zeroMode : mode = 0 <;>
            simp [dAtom, zeroMode, C, O, Module.End.mul_apply, ghostZero]
        · have matterZero := directionalCurrent_high D longitudinal matter mode above
          by_cases zeroMode : mode = 0 <;>
            simp [dAtom, zeroMode, C, O, Module.End.mul_apply, matterZero]
      constructor
      · by_contra notBelow
        exact nonzero (zeroOutside (Or.inl (lt_of_not_ge notBelow)))
      · by_contra notAbove
        exact nonzero (zeroOutside (Or.inr (lt_of_not_ge notAbove)))
  | add first second firstFinite secondFinite =>
      apply (firstFinite.union secondFinite).subset
      intro mode nonzero
      by_cases firstZero : dAtom D longitudinal mode first = 0
      · right
        intro secondZero
        exact nonzero (by simp [map_add, firstZero, secondZero])
      · exact Or.inl firstZero

theorem rAtom_finite (D : LatticeData) (nullDirection : Fin D.rank → ℂ)
    (state : State D) :
    Function.HasFiniteSupport (fun mode : ℤ => rAtom D nullDirection mode state) := by
  induction state using TensorProduct.induction_on with
  | zero => simp [Function.HasFiniteSupport]
  | tmul matter ghost =>
      apply (Set.finite_Icc (-(vectorFrequencyBound D matter : ℤ))
        ((((occupied ghost).sup id : ℕ) : ℤ) + 4)).subset
      intro mode nonzero
      have zeroOutside (outside :
          mode < -(vectorFrequencyBound D matter : ℤ) ∨
            (((occupied ghost).sup id : ℕ) : ℤ) + 4 < mode) :
          rAtom D nullDirection mode (matter ⊗ₜ[ℂ] ghost) = 0 := by
        rcases outside with below | above
        · have matterZero := directionalCurrent_high D nullDirection matter (-mode)
            (by omega)
          by_cases zeroMode : mode = 0 <;>
            simp [rAtom, zeroMode, B, O, Module.End.mul_apply, matterZero]
        · have ghostZero := b_high ghost mode above
          by_cases zeroMode : mode = 0 <;>
            simp [rAtom, zeroMode, B, O, Module.End.mul_apply, ghostZero]
      constructor
      · by_contra notBelow
        exact nonzero (zeroOutside (Or.inl (lt_of_not_ge notBelow)))
      · by_contra notAbove
        exact nonzero (zeroOutside (Or.inr (lt_of_not_ge notAbove)))
  | add first second firstFinite secondFinite =>
      apply (firstFinite.union secondFinite).subset
      intro mode nonzero
      by_cases firstZero : rAtom D nullDirection mode first = 0
      · right
        intro secondZero
        exact nonzero (by simp [map_add, firstZero, secondZero])
      · exact Or.inl firstZero

def dSum (D : LatticeData) (longitudinal : Fin D.rank → ℂ) :
    Module.End ℂ (State D) where
  toFun state := ∑ᶠ mode : ℤ, dAtom D longitudinal mode state
  map_add' first second := by
    simp only [map_add]
    exact finsum_add_distrib (dAtom_finite D longitudinal first)
      (dAtom_finite D longitudinal second)
  map_smul' scalar state := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' scalar (dAtom_finite D longitudinal state)).symm

def rSum (D : LatticeData) (nullDirection : Fin D.rank → ℂ) :
    Module.End ℂ (State D) where
  toFun state := ∑ᶠ mode : ℤ, rAtom D nullDirection mode state
  map_add' first second := by
    simp only [map_add]
    exact finsum_add_distrib (rAtom_finite D nullDirection first)
      (rAtom_finite D nullDirection second)
  map_smul' scalar state := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' scalar (rAtom_finite D nullDirection state)).symm

def delta (D : LatticeData) (longitudinal : Fin D.rank → ℂ) (chargeCoefficient : ℂ) :
    Module.End ℂ (State D) := chargeCoefficient • dSum D longitudinal

def R (D : LatticeData) (nullDirection : Fin D.rank → ℂ) (chargeCoefficient : ℂ) :
    Module.End ℂ (State D) := chargeCoefficient⁻¹ • rSum D nullDirection

def rawKAtom (D : LatticeData) (nullDirection longitudinal : Fin D.rank → ℂ)
    (mode : ℤ) : Module.End ℂ (State D) :=
  if mode = 0 then 0 else ((mode.natAbs : ℂ)⁻¹) •
    (O D nullDirection (-mode) * O D longitudinal mode +
      (mode : ℂ) • (C D (-mode) * B D mode))

def normalKAtom (D : LatticeData) (nullDirection longitudinal : Fin D.rank → ℂ)
    (mode : ℤ) : Module.End ℂ (State D) :=
  if mode = 0 then 0 else
    if 0 < mode then
      ((mode.natAbs : ℂ)⁻¹) • (O D nullDirection (-mode) * O D longitudinal mode) +
        C D (-mode) * B D mode
    else
      ((mode.natAbs : ℂ)⁻¹) • (O D longitudinal mode * O D nullDirection (-mode)) +
        B D mode * C D (-mode)

theorem dAtom_rAtom (D : LatticeData) (nullDirection longitudinal : Fin D.rank → ℂ)
    (dual : gramPair D longitudinal nullDirection = 1) (first second : ℤ) :
    dAtom D longitudinal first * rAtom D nullDirection second +
      rAtom D nullDirection second * dAtom D longitudinal first =
      if first = second then rawKAtom D nullDirection longitudinal second else 0 := by
  by_cases firstZero : first = 0
  · subst first
    by_cases secondZero : second = 0
    · simp [dAtom, rAtom, rawKAtom, secondZero]
    · simp [dAtom, rAtom, rawKAtom, secondZero, Ne.symm secondZero]
  by_cases secondZero : second = 0
  · subst second
    simp [dAtom, rAtom, rawKAtom, firstZero]
  have shuffle :
      C D (-first) * (O D nullDirection (-second) * O D longitudinal first) * B D second =
      O D nullDirection (-second) * (C D (-first) * B D second) * O D longitudinal first := by
    calc
      _ = (C D (-first) * O D nullDirection (-second)) *
          (O D longitudinal first * B D second) := by noncomm_ring
      _ = (O D nullDirection (-second) * C D (-first)) *
          (B D second * O D longitudinal first) := by
        rw [← O_C_commute, O_B_commute]
      _ = _ := by noncomm_ring
  have productIdentity :
      (C D (-first) * O D longitudinal first) *
          (O D nullDirection (-second) * B D second) +
        (O D nullDirection (-second) * B D second) *
          (C D (-first) * O D longitudinal first) =
      C D (-first) * (O D longitudinal first * O D nullDirection (-second) -
          O D nullDirection (-second) * O D longitudinal first) * B D second +
        O D nullDirection (-second) *
          (C D (-first) * B D second + B D second * C D (-first)) *
          O D longitudinal first := by
    simp only [mul_sub, sub_mul, mul_add, add_mul]
    rw [shuffle]
    noncomm_ring
  simp only [dAtom, rAtom, if_neg firstZero, if_neg secondZero,
    mul_smul_comm, smul_mul_assoc, ← smul_add]
  rw [productIdentity, O_heisenberg, C_B_anticommute]
  by_cases equalModes : first = second
  · subst first
    simp [rawKAtom, secondZero, dual, smul_mul_assoc, mul_smul_comm, add_comm]
  · have firstNonresonant : first + -second ≠ 0 := by omega
    have secondNonresonant : second + -first ≠ 0 := by omega
    simp [equalModes, firstNonresonant, secondNonresonant]

theorem rawKAtom_eq_normal (D : LatticeData)
    (nullDirection longitudinal : Fin D.rank → ℂ)
    (dual : gramPair D nullDirection longitudinal = 1) (mode : ℤ) :
    rawKAtom D nullDirection longitudinal mode =
      normalKAtom D nullDirection longitudinal mode := by
  by_cases zeroMode : mode = 0
  · simp [rawKAtom, normalKAtom, zeroMode]
  have castNonzero : (mode : ℂ) ≠ 0 := by exact_mod_cast zeroMode
  by_cases positive : 0 < mode
  · have absCast : (mode.natAbs : ℂ) = (mode : ℂ) := by
      have integerIdentity : (mode.natAbs : ℤ) = mode := by
        rw [Int.natCast_natAbs, abs_of_pos positive]
      simpa only [Int.cast_natCast] using congrArg (fun value : ℤ => (value : ℂ)) integerIdentity
    simp [rawKAtom, normalKAtom, zeroMode, positive, absCast, smul_add,
      smul_smul, inv_mul_cancel₀ castNonzero]
  · have negative : mode < 0 := by omega
    have absCast : (mode.natAbs : ℂ) = -(mode : ℂ) := by
      have integerIdentity : (mode.natAbs : ℤ) = -mode := by
        rw [Int.natCast_natAbs, abs_of_neg negative]
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun value : ℤ => (value : ℂ)) integerIdentity
    have matterReorder : O D nullDirection (-mode) * O D longitudinal mode =
        O D longitudinal mode * O D nullDirection (-mode) -
          (mode : ℂ) • (1 : Module.End ℂ (State D)) := by
      have commutator := O_heisenberg D nullDirection longitudinal (-mode) mode
      simp only [neg_add_cancel, if_true, dual, mul_one, Int.cast_neg] at commutator
      calc
        _ = (O D nullDirection (-mode) * O D longitudinal mode -
            O D longitudinal mode * O D nullDirection (-mode)) +
          O D longitudinal mode * O D nullDirection (-mode) := by abel
        _ = _ := by rw [commutator]; module
    have ghostReorder : C D (-mode) * B D mode =
        1 - B D mode * C D (-mode) := by
      have anticommutator := C_B_anticommute D (-mode) mode
      simp only [add_neg_cancel, if_true] at anticommutator
      calc
        _ = (C D (-mode) * B D mode + B D mode * C D (-mode)) -
          B D mode * C D (-mode) := by abel
        _ = _ := by rw [anticommutator]
    have scalarIdentity : (-(mode : ℂ))⁻¹ * (mode : ℂ) = -1 := by
      field_simp [castNonzero]
    simp only [rawKAtom, normalKAtom, if_neg zeroMode, if_neg positive,
      matterReorder, ghostReorder, absCast, smul_sub, smul_add, smul_smul]
    rw [scalarIdentity]
    module

theorem dSum_rAtom (D : LatticeData) (nullDirection longitudinal : Fin D.rank → ℂ)
    (dual : gramPair D longitudinal nullDirection = 1) (mode : ℤ) :
    dSum D longitudinal * rAtom D nullDirection mode +
      rAtom D nullDirection mode * dSum D longitudinal =
      rawKAtom D nullDirection longitudinal mode := by
  apply LinearMap.ext
  intro state
  have inputFinite := dAtom_finite D longitudinal state
  have outputFinite := dAtom_finite D longitudinal (rAtom D nullDirection mode state)
  have imageFinite := inputFinite.fun_comp (map_zero (rAtom D nullDirection mode))
  have mapped := (rAtom D nullDirection mode).toAddMonoidHom.map_finsum inputFinite
  simp only [LinearMap.toAddMonoidHom_coe] at mapped
  change (∑ᶠ first : ℤ, dAtom D longitudinal first (rAtom D nullDirection mode state)) +
    rAtom D nullDirection mode (∑ᶠ first : ℤ, dAtom D longitudinal first state) = _
  rw [mapped, ← finsum_add_distrib outputFinite imageFinite]
  have pointwise (first : ℤ) :
      dAtom D longitudinal first (rAtom D nullDirection mode state) +
        rAtom D nullDirection mode (dAtom D longitudinal first state) =
        if first = mode then rawKAtom D nullDirection longitudinal mode state else 0 := by
    have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
      (dAtom_rAtom D nullDirection longitudinal dual first mode)
    by_cases equalMode : first = mode <;>
      simpa only [LinearMap.add_apply, Module.End.mul_apply, equalMode,
        if_true, if_false, LinearMap.zero_apply] using operatorIdentity
  simp_rw [pointwise]
  simpa using (finsum_eq_single
    (fun first : ℤ => if first = mode then rawKAtom D nullDirection longitudinal mode state else 0)
    mode (by intro first distinct; simp [distinct]))

theorem rawKAtom_finite (D : LatticeData)
    (nullDirection longitudinal : Fin D.rank → ℂ)
    (dual : gramPair D longitudinal nullDirection = 1) (state : State D) :
    Function.HasFiniteSupport (fun mode : ℤ =>
      rawKAtom D nullDirection longitudinal mode state) := by
  have firstFinite := (rAtom_finite D nullDirection state).fun_comp
    (map_zero (dSum D longitudinal))
  have secondFinite := rAtom_finite D nullDirection (dSum D longitudinal state)
  apply (firstFinite.union secondFinite).subset
  intro mode nonzero
  have equality := congrArg (fun operator : Module.End ℂ (State D) => operator state)
    (dSum_rAtom D nullDirection longitudinal dual mode)
  simp only [LinearMap.add_apply, Module.End.mul_apply] at equality
  by_cases firstZero : dSum D longitudinal (rAtom D nullDirection mode state) = 0
  · right
    intro secondZero
    exact nonzero (equality.symm.trans (by simp only [firstZero, secondZero, add_zero]))
  · exact Or.inl firstZero

def K (D : LatticeData) (nullDirection longitudinal : Fin D.rank → ℂ)
    (dual : gramPair D longitudinal nullDirection = 1) : Module.End ℂ (State D) where
  toFun state := ∑ᶠ mode : ℤ, rawKAtom D nullDirection longitudinal mode state
  map_add' first second := by
    simp only [map_add]
    exact finsum_add_distrib (rawKAtom_finite D nullDirection longitudinal dual first)
      (rawKAtom_finite D nullDirection longitudinal dual second)
  map_smul' scalar state := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' scalar
      (rawKAtom_finite D nullDirection longitudinal dual state)).symm

theorem delta_R_anticommutator (D : LatticeData)
    (nullDirection longitudinal : Fin D.rank → ℂ)
    (dual : gramPair D longitudinal nullDirection = 1)
    (chargeCoefficient : ℂ) (nonzero : chargeCoefficient ≠ 0) :
    delta D longitudinal chargeCoefficient * R D nullDirection chargeCoefficient +
      R D nullDirection chargeCoefficient * delta D longitudinal chargeCoefficient =
      K D nullDirection longitudinal dual := by
  have unscaled : dSum D longitudinal * rSum D nullDirection +
      rSum D nullDirection * dSum D longitudinal = K D nullDirection longitudinal dual := by
    apply LinearMap.ext
    intro state
    have inputFinite := rAtom_finite D nullDirection state
    have outputFinite := rAtom_finite D nullDirection (dSum D longitudinal state)
    have imageFinite := inputFinite.fun_comp (map_zero (dSum D longitudinal))
    have mapped := (dSum D longitudinal).toAddMonoidHom.map_finsum inputFinite
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change dSum D longitudinal (∑ᶠ mode : ℤ, rAtom D nullDirection mode state) +
      (∑ᶠ mode : ℤ, rAtom D nullDirection mode (dSum D longitudinal state)) = _
    rw [mapped, ← finsum_add_distrib imageFinite outputFinite]
    apply finsum_congr
    intro mode
    have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
      (dSum_rAtom D nullDirection longitudinal dual mode)
    simpa only [LinearMap.add_apply, Module.End.mul_apply] using operatorIdentity
  simpa only [delta, R, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ nonzero, inv_mul_cancel₀ nonzero, one_smul] using unscaled

theorem K_normal_ordered (D : LatticeData)
    (nullDirection longitudinal : Fin D.rank → ℂ)
    (dual : gramPair D longitudinal nullDirection = 1) (state : State D) :
    K D nullDirection longitudinal dual state =
      ∑ᶠ mode : ℤ, normalKAtom D nullDirection longitudinal mode state := by
  have oppositeDual : gramPair D nullDirection longitudinal = 1 := by
    rw [gramPair_symm, dual]
  change (∑ᶠ mode : ℤ, rawKAtom D nullDirection longitudinal mode state) = _
  apply finsum_congr
  intro mode
  rw [rawKAtom_eq_normal D nullDirection longitudinal oppositeDual]

theorem dAtom_anticommute (D : LatticeData) (longitudinal : Fin D.rank → ℂ)
    (null : gramPair D longitudinal longitudinal = 0) (first second : ℤ) :
    dAtom D longitudinal first * dAtom D longitudinal second +
      dAtom D longitudinal second * dAtom D longitudinal first = 0 := by
  by_cases firstZero : first = 0 <;> by_cases secondZero : second = 0
  · simp [dAtom, firstZero, secondZero]
  · simp [dAtom, firstZero]
  · simp [dAtom, secondZero]
  · have matterCommute : O D longitudinal first * O D longitudinal second =
        O D longitudinal second * O D longitudinal first := by
      have commutator := O_heisenberg D longitudinal longitudinal first second
      simp [null] at commutator
      exact sub_eq_zero.mp commutator
    simp only [dAtom, if_neg firstZero, if_neg secondZero]
    calc
      _ = (C D (-first) * C D (-second)) *
          (O D longitudinal first * O D longitudinal second) +
        (C D (-second) * C D (-first)) *
          (O D longitudinal second * O D longitudinal first) := by
        simp only [mul_assoc]
        rw [← mul_assoc (O D longitudinal first) (C D (-second)), O_C_commute,
          ← mul_assoc (O D longitudinal second) (C D (-first)), O_C_commute]
        noncomm_ring
      _ = (C D (-first) * C D (-second) + C D (-second) * C D (-first)) *
          (O D longitudinal first * O D longitudinal second) := by
        rw [← matterCommute, add_mul]
      _ = 0 := by rw [C_C_anticommute, zero_mul]

theorem rAtom_anticommute (D : LatticeData) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) (first second : ℤ) :
    rAtom D nullDirection first * rAtom D nullDirection second +
      rAtom D nullDirection second * rAtom D nullDirection first = 0 := by
  by_cases firstZero : first = 0 <;> by_cases secondZero : second = 0
  · simp [rAtom, firstZero, secondZero]
  · simp [rAtom, firstZero]
  · simp [rAtom, secondZero]
  · have matterCommute : O D nullDirection (-first) * O D nullDirection (-second) =
        O D nullDirection (-second) * O D nullDirection (-first) := by
      have commutator := O_heisenberg D nullDirection nullDirection (-first) (-second)
      simp [null] at commutator
      exact sub_eq_zero.mp commutator
    have unscaled :
        (O D nullDirection (-first) * B D first) *
            (O D nullDirection (-second) * B D second) +
          (O D nullDirection (-second) * B D second) *
            (O D nullDirection (-first) * B D first) = 0 := by
      calc
        _ = (O D nullDirection (-first) * O D nullDirection (-second)) *
            (B D first * B D second) +
          (O D nullDirection (-second) * O D nullDirection (-first)) *
            (B D second * B D first) := by
          simp only [mul_assoc]
          rw [← mul_assoc (B D first) (O D nullDirection (-second)), ← O_B_commute,
            ← mul_assoc (B D second) (O D nullDirection (-first)), ← O_B_commute]
          noncomm_ring
        _ = (O D nullDirection (-first) * O D nullDirection (-second)) *
            (B D first * B D second + B D second * B D first) := by
          rw [← matterCommute, mul_add]
        _ = 0 := by rw [B_B_anticommute, mul_zero]
    simp only [rAtom, if_neg firstZero, if_neg secondZero,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm ((second.natAbs : ℂ)⁻¹) ((first.natAbs : ℂ)⁻¹),
      ← smul_add, unscaled, smul_zero]

theorem dSum_square (D : LatticeData) (longitudinal : Fin D.rank → ℂ)
    (null : gramPair D longitudinal longitudinal = 0) :
    dSum D longitudinal * dSum D longitudinal = 0 := by
  have atomLaw (mode : ℤ) : dSum D longitudinal * dAtom D longitudinal mode +
      dAtom D longitudinal mode * dSum D longitudinal = 0 := by
    apply LinearMap.ext
    intro state
    have inputFinite := dAtom_finite D longitudinal state
    have outputFinite := dAtom_finite D longitudinal (dAtom D longitudinal mode state)
    have imageFinite := inputFinite.fun_comp (map_zero (dAtom D longitudinal mode))
    have mapped := (dAtom D longitudinal mode).toAddMonoidHom.map_finsum inputFinite
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change (∑ᶠ first : ℤ, dAtom D longitudinal first (dAtom D longitudinal mode state)) +
      dAtom D longitudinal mode (∑ᶠ first : ℤ, dAtom D longitudinal first state) = 0
    rw [mapped, ← finsum_add_distrib outputFinite imageFinite]
    have pointwise (first : ℤ) : dAtom D longitudinal first (dAtom D longitudinal mode state) +
        dAtom D longitudinal mode (dAtom D longitudinal first state) = 0 := by
      have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
        (dAtom_anticommute D longitudinal null first mode)
      simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
        using operatorIdentity
    simp_rw [pointwise]
    simp
  apply LinearMap.ext
  intro state
  have inputFinite := dAtom_finite D longitudinal state
  have outputFinite := dAtom_finite D longitudinal (dSum D longitudinal state)
  have imageFinite := inputFinite.fun_comp (map_zero (dSum D longitudinal))
  have mapped := (dSum D longitudinal).toAddMonoidHom.map_finsum inputFinite
  simp only [LinearMap.toAddMonoidHom_coe] at mapped
  have doubled : dSum D longitudinal (dSum D longitudinal state) +
      dSum D longitudinal (dSum D longitudinal state) = 0 := by
    change dSum D longitudinal (∑ᶠ mode : ℤ, dAtom D longitudinal mode state) +
      (∑ᶠ mode : ℤ, dAtom D longitudinal mode (dSum D longitudinal state)) = 0
    rw [mapped, ← finsum_add_distrib imageFinite outputFinite]
    have pointwise (mode : ℤ) : dSum D longitudinal (dAtom D longitudinal mode state) +
        dAtom D longitudinal mode (dSum D longitudinal state) = 0 := by
      have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
        (atomLaw mode)
      simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
        using operatorIdentity
    simp_rw [pointwise]
    simp
  have scalarZero : (2 : ℂ) • dSum D longitudinal (dSum D longitudinal state) = 0 := by
    simpa only [two_smul] using doubled
  exact (smul_eq_zero.mp scalarZero).resolve_left (by norm_num)

theorem rSum_square (D : LatticeData) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) :
    rSum D nullDirection * rSum D nullDirection = 0 := by
  have atomLaw (mode : ℤ) : rSum D nullDirection * rAtom D nullDirection mode +
      rAtom D nullDirection mode * rSum D nullDirection = 0 := by
    apply LinearMap.ext
    intro state
    have inputFinite := rAtom_finite D nullDirection state
    have outputFinite := rAtom_finite D nullDirection (rAtom D nullDirection mode state)
    have imageFinite := inputFinite.fun_comp (map_zero (rAtom D nullDirection mode))
    have mapped := (rAtom D nullDirection mode).toAddMonoidHom.map_finsum inputFinite
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change (∑ᶠ first : ℤ, rAtom D nullDirection first (rAtom D nullDirection mode state)) +
      rAtom D nullDirection mode (∑ᶠ first : ℤ, rAtom D nullDirection first state) = 0
    rw [mapped, ← finsum_add_distrib outputFinite imageFinite]
    have pointwise (first : ℤ) : rAtom D nullDirection first (rAtom D nullDirection mode state) +
        rAtom D nullDirection mode (rAtom D nullDirection first state) = 0 := by
      have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
        (rAtom_anticommute D nullDirection null first mode)
      simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
        using operatorIdentity
    simp_rw [pointwise]
    simp
  apply LinearMap.ext
  intro state
  have inputFinite := rAtom_finite D nullDirection state
  have outputFinite := rAtom_finite D nullDirection (rSum D nullDirection state)
  have imageFinite := inputFinite.fun_comp (map_zero (rSum D nullDirection))
  have mapped := (rSum D nullDirection).toAddMonoidHom.map_finsum inputFinite
  simp only [LinearMap.toAddMonoidHom_coe] at mapped
  have doubled : rSum D nullDirection (rSum D nullDirection state) +
      rSum D nullDirection (rSum D nullDirection state) = 0 := by
    change rSum D nullDirection (∑ᶠ mode : ℤ, rAtom D nullDirection mode state) +
      (∑ᶠ mode : ℤ, rAtom D nullDirection mode (rSum D nullDirection state)) = 0
    rw [mapped, ← finsum_add_distrib imageFinite outputFinite]
    have pointwise (mode : ℤ) : rSum D nullDirection (rAtom D nullDirection mode state) +
        rAtom D nullDirection mode (rSum D nullDirection state) = 0 := by
      have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
        (atomLaw mode)
      simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
        using operatorIdentity
    simp_rw [pointwise]
    simp
  have scalarZero : (2 : ℂ) • rSum D nullDirection (rSum D nullDirection state) = 0 := by
    simpa only [two_smul] using doubled
  exact (smul_eq_zero.mp scalarZero).resolve_left (by norm_num)

theorem J_dAtom (D : LatticeData) (longitudinal : Fin D.rank → ℂ) (mode : ℤ) :
    LatticeBcGhostBrstGhostNumber.J D * dAtom D longitudinal mode -
      dAtom D longitudinal mode * LatticeBcGhostBrstGhostNumber.J D =
      dAtom D longitudinal mode := by
  by_cases zeroMode : mode = 0
  · simp [dAtom, zeroMode]
  have ghostGrading : LatticeBcGhostBrstGhostNumber.J D * C D (-mode) -
      C D (-mode) * LatticeBcGhostBrstGhostNumber.J D = C D (-mode) := by
    have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
      (BcGhostNumber.J_c_commutator (K := ℂ) (-mode))
    simp only [map_sub, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
    simpa only [LatticeBcGhostBrstGhostNumber.J, C, LinearMap.lTensor_def] using lifted
  have matterCommute : LatticeBcGhostBrstGhostNumber.J D * O D longitudinal mode =
      O D longitudinal mode * LatticeBcGhostBrstGhostNumber.J D := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [LatticeBcGhostBrstGhostNumber.J, O, Module.End.mul_apply]
  simp only [dAtom, if_neg zeroMode]
  calc
    _ = (LatticeBcGhostBrstGhostNumber.J D * C D (-mode) -
          C D (-mode) * LatticeBcGhostBrstGhostNumber.J D) * O D longitudinal mode +
        C D (-mode) * (LatticeBcGhostBrstGhostNumber.J D * O D longitudinal mode -
          O D longitudinal mode * LatticeBcGhostBrstGhostNumber.J D) := by
        simp only [mul_sub, sub_mul, mul_assoc]
        abel
    _ = _ := by rw [ghostGrading, matterCommute, sub_self]; simp

theorem J_delta (D : LatticeData) (longitudinal : Fin D.rank → ℂ)
    (chargeCoefficient : ℂ) :
    LatticeBcGhostBrstGhostNumber.J D * delta D longitudinal chargeCoefficient -
      delta D longitudinal chargeCoefficient * LatticeBcGhostBrstGhostNumber.J D =
      delta D longitudinal chargeCoefficient := by
  have unscaled : LatticeBcGhostBrstGhostNumber.J D * dSum D longitudinal -
      dSum D longitudinal * LatticeBcGhostBrstGhostNumber.J D = dSum D longitudinal := by
    apply LinearMap.ext
    intro state
    have inputFinite := dAtom_finite D longitudinal state
    have outputFinite := dAtom_finite D longitudinal (LatticeBcGhostBrstGhostNumber.J D state)
    have imageFinite := inputFinite.fun_comp (map_zero (LatticeBcGhostBrstGhostNumber.J D))
    have mapped := (LatticeBcGhostBrstGhostNumber.J D).toAddMonoidHom.map_finsum inputFinite
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change LatticeBcGhostBrstGhostNumber.J D (∑ᶠ mode : ℤ, dAtom D longitudinal mode state) -
      (∑ᶠ mode : ℤ, dAtom D longitudinal mode (LatticeBcGhostBrstGhostNumber.J D state)) = _
    rw [mapped, ← finsum_sub_distrib imageFinite outputFinite]
    apply finsum_congr
    intro mode
    have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
      (J_dAtom D longitudinal mode)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply] using operatorIdentity
  simpa only [delta, mul_smul_comm, smul_mul_assoc, smul_sub] using
    congrArg (fun operator : Module.End ℂ (State D) => chargeCoefficient • operator) unscaled

theorem original_Q_quartet_algebra (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (nullDirection longitudinal : Fin D.rank → ℂ)
    (nullLeft : gramPair D nullDirection nullDirection = 0)
    (nullRight : gramPair D longitudinal longitudinal = 0)
    (dual : gramPair D longitudinal nullDirection = 1)
    (chargeCoefficient : ℂ) (nonzero : chargeCoefficient ≠ 0) :
    delta D longitudinal chargeCoefficient * delta D longitudinal chargeCoefficient = 0 ∧
    R D nullDirection chargeCoefficient * R D nullDirection chargeCoefficient = 0 ∧
    delta D longitudinal chargeCoefficient * R D nullDirection chargeCoefficient +
      R D nullDirection chargeCoefficient * delta D longitudinal chargeCoefficient =
      K D nullDirection longitudinal dual ∧
    (∀ state : State D, K D nullDirection longitudinal dual state =
      ∑ᶠ mode : ℤ, normalKAtom D nullDirection longitudinal mode state) ∧
    LatticeBcGhostBrstGhostNumber.J D * (Q D H - delta D longitudinal chargeCoefficient) -
      (Q D H - delta D longitudinal chargeCoefficient) * LatticeBcGhostBrstGhostNumber.J D =
      Q D H - delta D longitudinal chargeCoefficient := by
  refine ⟨?_, ?_, delta_R_anticommutator D nullDirection longitudinal dual
    chargeCoefficient nonzero, K_normal_ordered D nullDirection longitudinal dual, ?_⟩
  · simp only [delta, smul_mul_assoc, mul_smul_comm, smul_smul,
      dSum_square D longitudinal nullRight, smul_zero]
  · simp only [R, smul_mul_assoc, mul_smul_comm, smul_smul,
      rSum_square D nullDirection nullLeft, smul_zero]
  · have originalLaw := LatticeBcGhostBrstGhostNumber.J_Q_commutator D H
    have leadingLaw := J_delta D longitudinal chargeCoefficient
    calc
      _ = (LatticeBcGhostBrstGhostNumber.J D * Q D H -
            Q D H * LatticeBcGhostBrstGhostNumber.J D) -
          (LatticeBcGhostBrstGhostNumber.J D * delta D longitudinal chargeCoefficient -
            delta D longitudinal chargeCoefficient * LatticeBcGhostBrstGhostNumber.J D) := by
        simp only [mul_sub, sub_mul]
        abel
      _ = _ := by rw [originalLaw, leadingLaw]

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
