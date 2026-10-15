import D5.S3.VertexAlgebra.OriginalQFiniteTransferLawsTransient
import D5.S3.VertexAlgebra.OriginalQFiniteHplAlgebraTransient

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def originalEnergySector (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) : Submodule ℂ (State D) where
  carrier := {state | chargeProjection D beta state = state ∧
    (M D H 0 + G D 0) state = (chosenH D beta + (level : ℂ) - 1) • state}
  zero_mem' := by simp
  add_mem' := by
    intro first second firstMember secondMember
    constructor
    · rw [map_add, firstMember.1, secondMember.1]
    · rw [map_add, firstMember.2, secondMember.2, smul_add]
  smul_mem' := by
    intro scalar state member
    constructor
    · rw [map_smul, member.1]
    · rw [map_smul, member.2, smul_comm]

def restrictEnergyOperator (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (operator : Module.End ℂ (State D))
    (sectorLaw : ∀ state, chargeProjection D beta state = state →
      chargeProjection D beta (operator state) = operator state)
    (energyLaw : (M D H 0 + G D 0) * operator = operator * (M D H 0 + G D 0)) :
    Module.End ℂ (originalEnergySector D H beta level) :=
  operator.restrict (by
    intro state member
    constructor
    · exact sectorLaw state member.1
    · have equality := LinearMap.congr_fun energyLaw state
      simpa only [Module.End.mul_apply, member.2, map_smul] using equality)

variable (D : LatticeData)
variable (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank) (level : ℤ)

local notation "totalZero" => M D H 0 + G D 0
local notation "normalized" => S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
  (chosenP D beta nullDirection)
local notation "leading" => delta D (adaptedPartner D beta nullDirection) (chosenP D beta nullDirection)
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
elab "terminationSupplier" suffix:str : term => do
  let environment ← Lean.getEnv
  let target := "_private.D5.S3.VertexAlgebra.LatticeBcGhostPerturbationTermination.0." ++
    "D5.S3.VertexAlgebra.OriginalQQuartetSource." ++ suffix.getString
  let some entry := environment.constants.toList.find? (fun entry => entry.1.toString == target)
    | throwError "Missing exact original supplier: {target}"
  return Lean.mkConst entry.1

local notation "actualQSector" => terminationSupplier "Q_sector"
local notation "actualDSector" => terminationSupplier "dSum_sector"
local notation "actualSSector" => terminationSupplier "normalized_sector"
local notation "actualQEnergy" => terminationSupplier "totalZero_Q_commutes"
local notation "actualDEnergy" => terminationSupplier "totalZero_dSum_commutes"

def energyOriginalQ : Module.End ℂ (originalEnergySector D H beta level) :=
  restrictEnergyOperator D H beta level (Q D H) (actualQSector D H beta)
    (actualQEnergy D H leftGramInverse rightGramInverse)

def energyLeading : Module.End ℂ (originalEnergySector D H beta level) :=
  restrictEnergyOperator D H beta level leading
    (by
      intro state sector
      simp only [delta, LinearMap.smul_apply, map_smul,
        actualDSector D (adaptedPartner D beta nullDirection) beta state sector])
    (by
      simp only [delta, mul_smul_comm, smul_mul_assoc,
        actualDEnergy D H leftGramInverse rightGramInverse])

def energyNormalizer : Module.End ℂ (originalEnergySector D H beta level) :=
  restrictEnergyOperator D H beta level normalized
    (actualSSector D frame inverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis)
    (native_totalZero_S_commutes D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis H leftGramInverse rightGramInverse (chosenP D beta nullDirection))

def energyProjector : Module.End ℂ (originalEnergySector D H beta level) :=
  restrictEnergyOperator D H beta level projector
    (by
      intro state sector
      rw [← native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta state sector]
      simp only [map_sum, map_smul]
      have onWord (index : NativeIndex D) :
          projector (nativeWord D frame beta index) =
            (if kappa D xAxis yAxis index.1 index.2 = 0 then 1 else 0 : ℂ) •
              nativeWord D frame beta index :=
        P_native D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis beta index.1 1 index.2
      simp only [onWord, map_smul, nativeWord_sector])
    (native_totalZero_Kdagger_P_commute D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis H leftGramInverse rightGramInverse).2

local notation "energyQ" => energyOriginalQ D H leftGramInverse rightGramInverse beta level
local notation "energyDelta" => energyLeading D H leftGramInverse rightGramInverse beta nullDirection level
local notation "energyS" => energyNormalizer D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyP" => energyProjector D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta xAxis yAxis level

@[simp] theorem energyOriginalQ_coe (state : originalEnergySector D H beta level) :
    (energyQ state : State D) = Q D H state := rfl

@[simp] theorem energyLeading_coe (state : originalEnergySector D H beta level) :
    (energyDelta state : State D) = leading state := rfl

@[simp] theorem energyNormalizer_coe (state : originalEnergySector D H beta level) :
    (energyS state : State D) = normalized state := rfl

@[simp] theorem energyProjector_coe (state : originalEnergySector D H beta level) :
    (energyP state : State D) = projector state := rfl

theorem energy_correction_pow_coe (steps : ℕ) (state : originalEnergySector D H beta level) :
    (((energyS * (energyQ - energyDelta)) ^ steps) state : State D) =
      ((normalized * (Q D H - leading)) ^ steps) state := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis =>
    simp only [pow_succ', Module.End.mul_apply, energyNormalizer_coe, LinearMap.sub_apply,
      Submodule.coe_sub, energyOriginalQ_coe, energyLeading_coe, inductionHypothesis]

theorem energy_correction_nilpotent
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    (energyS * (energyQ - energyDelta)) ^ (2 * level.toNat + 2) = 0 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  rw [energy_correction_pow_coe]
  exact original_normalized_perturbation_termination D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
    xAxis yAxis null nonzero distinct xRow yRow xDual yDual level state state.property.1 state.property.2

def energyCorrectionInverse : Module.End ℂ (originalEnergySector D H beta level) :=
  ∑ steps ∈ Finset.range (2 * level.toNat + 2), (-(energyS * (energyQ - energyDelta))) ^ steps

local notation "energyInverse" => energyCorrectionInverse D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level

def energyTransferInclusion : Module.End ℂ (originalEnergySector D H beta level) := energyInverse * energyP

def energyTransferHomotopy : Module.End ℂ (originalEnergySector D H beta level) := energyInverse * energyS

def energyTransferProjection : Module.End ℂ (originalEnergySector D H beta level) :=
  energyP * (1 - (energyQ - energyDelta) * (energyInverse * energyS))

def energyTransferredDifferential : Module.End ℂ (originalEnergySector D H beta level) :=
  energyP * (energyQ - energyDelta) * energyInverse * energyP

local notation "energyInclusion" => energyTransferInclusion D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyHomotopy" => energyTransferHomotopy D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyProjection" => energyTransferProjection D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyDifferential" => energyTransferredDifferential D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level

theorem energy_signed_correction_pow_coe (steps : ℕ) (state : originalEnergySector D H beta level) :
    (((-(energyS * (energyQ - energyDelta))) ^ steps) state : State D) =
      ((-(normalized * (Q D H - leading))) ^ steps) state := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, Submodule.coe_neg,
      energyNormalizer_coe, LinearMap.sub_apply, Submodule.coe_sub,
      energyOriginalQ_coe, energyLeading_coe, inductionHypothesis]

theorem energyCorrectionInverse_coe (state : originalEnergySector D H beta level) :
    (energyInverse state : State D) = finiteOriginalCorrectionInverse D H frame inverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level state := by
  simp only [energyCorrectionInverse, finiteOriginalCorrectionInverse, LinearMap.sum_apply,
    Submodule.coe_sum, energy_signed_correction_pow_coe]

theorem energyTransferredDifferential_coe (state : originalEnergySector D H beta level) :
    (energyDifferential state : State D) = finiteOriginalTransferredDifferential D H frame inverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level state := by
  simp only [energyTransferredDifferential, finiteOriginalTransferredDifferential,
    Module.End.mul_apply, energyProjector_coe, LinearMap.sub_apply, Submodule.coe_sub,
    energyOriginalQ_coe, energyLeading_coe, energyCorrectionInverse_coe]

theorem original_energy_finite_transfer_laws
    (critical : D.rank = 26)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    energyQ * energyInclusion = energyInclusion * energyDifferential ∧
      energyProjection * energyQ = energyDifferential * energyProjection ∧
      energyProjection * energyInclusion = energyP ∧
      energyQ * energyHomotopy + energyHomotopy * energyQ = 1 - energyInclusion * energyProjection ∧
      energyDifferential * energyDifferential = 0 := by
  have inverseLeft : energyInverse * (1 + energyS * (energyQ - energyDelta)) = 1 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    have inverseLaw := (original_finite_inverse_actions D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
      xRow yRow xDual yDual level state state.property.1 state.property.2).1
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_add, Submodule.coe_sub, energyOriginalQ_coe, energyLeading_coe,
      energyNormalizer_coe, energyCorrectionInverse_coe] using inverseLaw
  have inverseRight : (1 + energyS * (energyQ - energyDelta)) * energyInverse = 1 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    have inverseLaw := (original_finite_inverse_actions D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
      xRow yRow xDual yDual level state state.property.1 state.property.2).2
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_add, Submodule.coe_sub, energyOriginalQ_coe, energyLeading_coe,
      energyNormalizer_coe, energyCorrectionInverse_coe] using inverseLaw
  have native := original_correction_intertwiners D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis
    critical nonzero distinct xRow yRow xDual yDual
  have strong := original_chosen_normalized_strong_contraction D beta nullDirection
    frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct xRow yRow xDual yDual nonzero
  have qSquare : energyQ * energyQ = 0 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, energyOriginalQ_coe, LinearMap.zero_apply, Submodule.coe_zero]
      using LinearMap.congr_fun native.1 state.val
  have hSquare : energyS * energyS = 0 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, energyNormalizer_coe, LinearMap.zero_apply, Submodule.coe_zero]
      using LinearMap.congr_fun strong.2.1 state.val
  have contraction : energyDelta * energyS + energyS * energyDelta = 1 - energyP := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, energyLeading_coe, energyNormalizer_coe, LinearMap.add_apply,
      LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_add, Submodule.coe_sub, energyProjector_coe]
      using LinearMap.congr_fun strong.1 state.val
  have hProjector : energyS * energyP = 0 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, energyNormalizer_coe, energyProjector_coe,
      LinearMap.zero_apply, Submodule.coe_zero] using LinearMap.congr_fun strong.2.2.1 state.val
  have projectorH : energyP * energyS = 0 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, energyNormalizer_coe, energyProjector_coe,
      LinearMap.zero_apply, Submodule.coe_zero] using LinearMap.congr_fun strong.2.2.2.1 state.val
  have leadingProjector : energyDelta * energyP = 0 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, energyLeading_coe, energyProjector_coe,
      LinearMap.zero_apply, Submodule.coe_zero] using LinearMap.congr_fun strong.2.2.2.2.1 state.val
  have projectorSquare : energyP * energyP = energyP := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, energyProjector_coe] using LinearMap.congr_fun
      (native_P_idempotent D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis) state.val
  have correctionIdentity : (1 + energyS * (energyQ - energyDelta)) * energyQ =
      energyDelta * (1 + energyS * (energyQ - energyDelta)) + energyP * (energyQ - energyDelta) := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_add, Submodule.coe_sub, energyOriginalQ_coe, energyLeading_coe,
      energyNormalizer_coe, energyProjector_coe] using LinearMap.congr_fun native.2.2.1 state.val
  simpa only [energyTransferInclusion, energyTransferHomotopy, energyTransferProjection,
    energyTransferredDifferential, mul_assoc] using
      OriginalQFiniteHplCheck.finite_transfer_ring_laws energyDelta energyS energyP energyQ energyInverse
        qSquare hSquare contraction hProjector projectorH leadingProjector projectorSquare
        correctionIdentity inverseLeft inverseRight

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
