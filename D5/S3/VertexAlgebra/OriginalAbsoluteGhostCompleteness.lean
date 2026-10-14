/- GID: D5/S3/VertexAlgebra/OriginalAbsoluteGhostCompleteness
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual graded finite HPL produces relative representatives of absolute ghost-one cycles. -/

import D5.S3.VertexAlgebra.OriginalAbsoluteGhostSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.OriginalAbsoluteGhostCompleteness

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQQuartetSource OriginalBrstReassembly OriginalQPhysicalPairing
  OriginalAbsoluteGhostSupport

noncomputable section

elab "absoluteHomotopyDegreeSupplier" : term => do
  let environment ← Lean.getEnv
  let target := "_private.D5.S3.VertexAlgebra.OriginalQRelativeAmbientPreimage.0." ++
    "D5.S3.VertexAlgebra.OriginalQQuartetSource.native_transfer_homotopy_ghost_degree"
  let some entry := environment.constants.toList.find? (fun entry => entry.1.toString == target)
    | throwError "Missing exact original supplier: {target}"
  return Lean.mkConst entry.1

private theorem operator_ghost_degree (D : LatticeData)
    (operator : Module.End ℂ (State D)) (shift degree : ℤ)
    (law : LatticeBcGhostBrstGhostNumber.J D * operator -
      operator * LatticeBcGhostBrstGhostNumber.J D = (shift : ℂ) • operator)
    (state : State D) (homogeneous : state ∈ ghostPart D degree) :
    operator state ∈ ghostPart D (degree + shift) := by
  have eigen := (ghostPart_iff_number D degree state).mp homogeneous
  change LatticeBcGhostBrstGhostNumber.J D state = (degree : ℂ) • state at eigen
  have equation := LinearMap.congr_fun law state
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    eigen, map_smul] at equation
  apply (ghostPart_iff_number D (degree + shift) _).mpr
  change LatticeBcGhostBrstGhostNumber.J D (operator state) = _
  simpa only [Int.cast_add, add_smul, add_comm] using (sub_eq_iff_eq_add).mp equation

variable (D : LatticeData) (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
variable (leftFrame : inverse * frame = 1) (rightFrame : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank) (level : ℤ)

local notation "sector" => originalEnergySector D H beta level
local notation "normalizer" => S D frame inverse leftFrame rightFrame xAxis yAxis
  (chosenP D beta nullDirection)
local notation "projector" => P D frame inverse leftFrame rightFrame xAxis yAxis
local notation "perturbation" => Q D H - delta D (adaptedPartner D beta nullDirection)
  (chosenP D beta nullDirection)
local notation "finiteInverse" => finiteOriginalCorrectionInverse D H frame inverse
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyQ" => energyOriginalQ D H leftGram rightGram beta level
local notation "energyP" => energyProjector D H frame inverse leftGram rightGram
  leftFrame rightFrame beta xAxis yAxis level
local notation "energyI" => energyTransferInclusion D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyR" => energyTransferProjection D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyHomotopy" => energyTransferHomotopy D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level

theorem inverse_ghost (degree : ℤ) (state : State D)
    (homogeneous : state ∈ ghostPart D degree) :
    finiteInverse state ∈ ghostPart D degree := by
  simpa only [add_zero] using operator_ghost_degree D finiteInverse 0 degree
    (by simpa using (J0_finite_correction_inverse_commutator D H frame inverse
      leftFrame rightFrame beta nullDirection xAxis yAxis level)) state homogeneous

theorem projector_ghost (degree : ℤ) (state : State D)
    (homogeneous : state ∈ ghostPart D degree) : projector state ∈ ghostPart D degree := by
  simpa only [add_zero] using operator_ghost_degree D projector 0 degree
    (by simpa using J0_P_commutator D frame inverse leftFrame rightFrame xAxis yAxis)
    state homogeneous

theorem energyHomotopy_ghost (degree : ℤ) (state : sector)
    (homogeneous : state.val ∈ ghostPart D degree) :
    (energyHomotopy state).val ∈ ghostPart D (degree - 1) := by
  exact absoluteHomotopyDegreeSupplier D H frame inverse leftGram rightGram leftFrame
    rightFrame beta nullDirection xAxis yAxis level degree state homogeneous

theorem energyInclusion_ghost (degree : ℤ) (state : sector)
    (homogeneous : state.val ∈ ghostPart D degree) :
    (energyI state).val ∈ ghostPart D degree := by
  simp only [energyTransferInclusion, Module.End.mul_apply,
    energyCorrectionInverse_coe, energyProjector_coe]
  exact inverse_ghost D H frame inverse leftFrame rightFrame beta nullDirection xAxis yAxis
    level degree _ (projector_ghost D frame inverse leftFrame rightFrame xAxis yAxis
      degree state.val homogeneous)

theorem energyProjection_ghost (degree : ℤ) (state : sector)
    (homogeneous : state.val ∈ ghostPart D degree) :
    (energyR state).val ∈ ghostPart D degree := by
  have lowered := energyHomotopy_ghost D H frame inverse leftGram rightGram leftFrame
    rightFrame beta nullDirection xAxis yAxis level degree state homogeneous
  have raised : perturbation (energyHomotopy state).val ∈ ghostPart D degree := by
    simpa only [sub_add_cancel] using operator_ghost_degree D perturbation 1 (degree - 1)
      (by simpa using (J0_Delta_commutator D H (adaptedPartner D beta nullDirection)
        (chosenP D beta nullDirection))) (energyHomotopy state).val lowered
  have difference := (ghostPart D degree).sub_mem homogeneous raised
  have projected := projector_ghost D frame inverse leftFrame rightFrame xAxis yAxis
    degree _ difference
  simpa only [energyTransferProjection, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, Submodule.coe_sub, energyProjector_coe, energyOriginalQ_coe,
    energyLeading_coe, energyTransferHomotopy] using projected

theorem energyProjection_fixed (state : sector) :
    projector (energyR state).val = (energyR state).val := by
  obtain ⟨preimage, equation⟩ := (energyReducedProjection D H frame inverse leftGram
    rightGram leftFrame rightFrame beta nullDirection xAxis yAxis level state).property
  change energyP preimage = energyR state at equation
  have fixedEnergy : energyP (energyR state) = energyR state := by
    rw [← equation]
    apply Subtype.ext
    simp only [energyProjector_coe]
    exact LinearMap.congr_fun
      (native_P_idempotent D frame inverse leftFrame rightFrame xAxis yAxis) preimage.val
  exact congrArg Subtype.val fixedEnergy

variable (critical : D.rank = 26) (null : gramPair D nullDirection nullDirection = 0)
variable (nonzero : chosenP D beta nullDirection ≠ 0) (distinct : xAxis ≠ yAxis)
variable (xRow : frame xAxis = nullDirection)
variable (yRow : frame yAxis = adaptedPartner D beta nullDirection)
variable (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
variable (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
variable (shell : chosenH D beta + (level : ℂ) - 1 = 0)

include critical null nonzero distinct xRow yRow xDual yDual in
theorem cycle_homotopy_boundary (state : sector) (cycle : Q D H state.val = 0) :
    state.val - (energyI (energyR state)).val = Q D H (energyHomotopy state).val := by
  have energyCycle : energyQ state = 0 := Subtype.ext cycle
  have identity := LinearMap.congr_fun
    (original_energy_finite_transfer_laws D H frame inverse leftGram rightGram
      leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero
      distinct xRow yRow xDual yDual).2.2.2.1 state
  have equality : energyQ (energyHomotopy state) = state - energyI (energyR state) := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, energyCycle, map_zero, add_zero,
      LinearMap.sub_apply, Module.End.one_apply] using identity
  exact (congrArg Subtype.val equality).symm

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct xRow yRow xDual yDual shell in
theorem absolute_ghost_one_representative (state : sector)
    (cycle : Q D H state.val = 0) (homogeneous : state.val ∈ ghostPart D 1) :
    ∃ representative : physicalCycles D H beta level,
      ∃ preimage : sector, preimage.val ∈ ghostPart D 0 ∧
        state.val - physicalState D H beta level representative = Q D H preimage.val := by
  let projected := energyR state
  let included := energyI projected
  have projectedDegree : projected.val ∈ ghostPart D 1 :=
    energyProjection_ghost D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level 1 state homogeneous
  have projectedB : B D 0 projected.val = 0 :=
    ghost_one_projector_relative D frame inverse leftFrame rightFrame beta xAxis yAxis
      projected.val projected.property.1
      (energyProjection_fixed D H frame inverse leftGram rightGram leftFrame rightFrame
        beta nullDirection xAxis yAxis level state) projectedDegree
  have antighost := LinearMap.congr_fun
    (energy_B0_transfer_compatibility_on_shell D H frame inverse leftGram rightGram
      leftFrame rightFrame beta nullDirection xAxis yAxis level xDual yDual nonzero shell).2.1
      projected
  have projectedEnergyB : energyB0 D H beta level projected = 0 := Subtype.ext projectedB
  have includedB : B D 0 included.val = 0 := by
    have equality : energyB0 D H beta level included = 0 := by
      simpa only [Module.End.mul_apply, projectedEnergyB, map_zero] using antighost
    exact congrArg Subtype.val equality
  have boundary := cycle_homotopy_boundary D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero
    distinct xRow yRow xDual yDual state cycle
  have includedCycle : Q D H included.val = 0 := by
    have mapped := congrArg (Q D H) boundary
    rw [map_sub, cycle, actual_square_zero D H leftGram rightGram critical] at mapped
    exact neg_eq_zero.mp (by simpa only [zero_sub] using mapped)
  have includedDegree := energyInclusion_ghost D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis level 1 projected projectedDegree
  refine ⟨⟨⟨included.val, includedCycle⟩,
    ⟨⟨included.property, includedB⟩, includedDegree⟩⟩, energyHomotopy state, ?_, boundary⟩
  simpa using energyHomotopy_ghost D H frame inverse leftGram rightGram leftFrame rightFrame
    beta nullDirection xAxis yAxis level 1 state homogeneous

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct xRow yRow xDual yDual in
theorem other_ghost_cycle_boundary (degree : ℤ) (notOne : degree ≠ 1) (notTwo : degree ≠ 2)
    (state : sector) (cycle : Q D H state.val = 0)
    (homogeneous : state.val ∈ ghostPart D degree) :
    ∃ preimage : sector, preimage.val ∈ ghostPart D (degree - 1) ∧
      Q D H preimage.val = state.val := by
  have projectedDegree := energyProjection_ghost D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis level degree state homogeneous
  have projectedZero : (energyR state).val = 0 :=
    projector_other_ghost_vanishes D frame inverse leftFrame rightFrame beta xAxis yAxis
      degree notOne notTwo (energyR state).val (energyR state).property.1
      (energyProjection_fixed D H frame inverse leftGram rightGram leftFrame rightFrame
        beta nullDirection xAxis yAxis level state) projectedDegree
  have zero : energyR state = 0 := Subtype.ext projectedZero
  have boundary := cycle_homotopy_boundary D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero
    distinct xRow yRow xDual yDual state cycle
  rw [zero, map_zero, Submodule.coe_zero, sub_zero] at boundary
  exact ⟨energyHomotopy state,
    energyHomotopy_ghost D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level degree state homogeneous, boundary.symm⟩

#print axioms absolute_ghost_one_representative
#print axioms other_ghost_cycle_boundary

end
end D5.S3.VertexAlgebra.OriginalAbsoluteGhostCompleteness
