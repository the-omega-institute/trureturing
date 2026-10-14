/- GID: D5/S3/VertexAlgebra/OriginalAbsoluteGhostDoublet
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual transferred up representatives compute the original absolute degree-two quotient. -/

import D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.OriginalAbsoluteGhostDoublet

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  BcGhostFockSupport OriginalQQuartetSource OriginalQEnergyInclusionPairing
  OriginalBrstReassembly OriginalAbsoluteGhostSupport OriginalAbsoluteGhostCompleteness
  RelativePairing.NativeTransverseCoordinates RelativePairing.AbsolutePhysicalNoGhost
open scoped BigOperators TensorProduct

noncomputable section

elab "absoluteEnergyDifferentialSupplier" : term => do
  let environment ← Lean.getEnv
  let target := "_private.D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization.0." ++
    "D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization.differential_zero"
  let some entry := environment.constants.toList.find? (fun entry => entry.1.toString == target)
    | throwError "Missing exact original supplier: {target}"
  return Lean.mkConst entry.1

variable (D : LatticeData) (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
variable (leftFrame : inverse * frame = 1) (rightFrame : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank) (level : ℤ)

local notation "coefficients" => TransverseDownIndex D xAxis yAxis level →₀ ℂ
local notation "sector" => originalEnergySector D H beta level
local notation "energyQ" => energyOriginalQ D H leftGram rightGram beta level
local notation "energyP" => energyProjector D H frame inverse leftGram rightGram
  leftFrame rightFrame beta xAxis yAxis level
local notation "energyI" => energyTransferInclusion D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyR" => energyTransferProjection D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyDiff" => energyTransferredDifferential D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyHomotopy" => energyTransferHomotopy D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level

def upIndex (powers : TransverseDownIndex D xAxis yAxis level) : NativeIndex D :=
  (powers.val, {3})

private theorem upIndex_injective : Function.Injective (upIndex D xAxis yAxis level) := by
  intro first second equation
  exact Subtype.ext (congrArg Prod.fst equation)

def upCoordinates : State D →ₗ[ℂ] coefficients :=
  (Finsupp.lcomapDomain (upIndex D xAxis yAxis level)
    (upIndex_injective D xAxis yAxis level)).comp
      (nativeCoefficients D frame inverse leftFrame rightFrame beta)

def upState : coefficients →ₗ[ℂ] State D :=
  Finsupp.linearCombination ℂ (fun powers => nativeWord D frame beta (powers.val, {3}))

theorem upCoordinates_upState (values : coefficients) :
    upCoordinates D frame inverse leftFrame rightFrame beta xAxis yAxis level
      (upState D frame beta xAxis yAxis level values) = values := by
  classical
  induction values using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof => simp only [map_add, firstProof, secondProof]
  | single powers scalar =>
    ext target
    simp only [upState, Finsupp.linearCombination_single, upCoordinates,
      LinearMap.comp_apply, map_smul, nativeCoefficients_word,
      Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.smul_apply]
    simp [upIndex, Finsupp.single_apply, Subtype.ext_iff]

private theorem native_up_level (powers : Index D →₀ ℕ) :
    nativeLevel D powers {3} = nativeLevel D powers ∅ := by
  norm_num [nativeLevel, polarizedLevel, polarizedWeight, BcGhostLZeroSpectrum.siteWeight]

include leftGram rightGram in
theorem upState_coordinates (state : sector)
    (fixed : P D frame inverse leftFrame rightFrame xAxis yAxis state.val = state.val)
    (homogeneous : state.val ∈ ghostPart D 2) :
    upState D frame beta xAxis yAxis level
      (upCoordinates D frame inverse leftFrame rightFrame beta xAxis yAxis level state.val) =
      state.val := by
  classical
  let values := nativeCoefficients D frame inverse leftFrame rightFrame beta state.val
  have supported (index : NativeIndex D) (member : index ∈ values.support) :
      ∃ powers : TransverseDownIndex D xAxis yAxis level,
        upIndex D xAxis yAxis level powers = index := by
    have nonzero : values index ≠ 0 := Finsupp.mem_support_iff.mp member
    have branches := projector_ghost_support D frame inverse leftFrame rightFrame beta
      xAxis yAxis 2 state.val state.property.1 fixed homogeneous index nonzero
    have singleton : index.2 = {3} := by
      rcases branches with branch | branch
      · omega
      · exact branch.1
    have diagonal := projector_coordinates D frame inverse leftFrame rightFrame beta
      xAxis yAxis state.val state.property.1 index
    rw [fixed] at diagonal
    have occupation : kappa D xAxis yAxis index.1 index.2 = 0 := by
      by_contra different
      rw [if_neg different] at diagonal
      exact nonzero diagonal
    have transverse := (kappa_zero_iff D xAxis yAxis index.1 index.2).mp occupation
    have atLevel := nativeT0_support_level D frame inverse leftFrame rightFrame beta H
      leftGram rightGram level state.val state.property.1 state.property.2 index nonzero
    refine ⟨⟨index.1, transverse.1, transverse.2.1, ?_⟩, ?_⟩
    · rw [singleton, native_up_level] at atLevel
      exact atLevel
    · exact Prod.ext rfl singleton.symm
  have bijective : Set.BijOn (upIndex D xAxis yAxis level)
      ((upIndex D xAxis yAxis level) ⁻¹' ↑values.support) ↑values.support := by
    refine ⟨fun _ member => member, (upIndex_injective D xAxis yAxis level).injOn, ?_⟩
    intro index member
    obtain ⟨powers, equation⟩ := supported index member
    exact ⟨powers, by change upIndex D xAxis yAxis level powers ∈ values.support
                      rw [equation]; exact member, equation⟩
  have sumRecovery := Finsupp.sum_comapDomain (upIndex D xAxis yAxis level) values
    (fun index scalar => scalar • nativeWord D frame beta index) bijective
  change (Finsupp.comapDomain (upIndex D xAxis yAxis level) values
    (upIndex_injective D xAxis yAxis level).injOn).sum
      (fun powers scalar => scalar • nativeWord D frame beta (powers.val, {3})) = state.val
  exact sumRecovery.trans (native_sector_finite_expansion D frame inverse leftFrame rightFrame
    beta state.val state.property.1)

def upInput : coefficients →ₗ[ℂ] LinearMap.range energyP :=
  Finsupp.linearCombination ℂ (fun powers => by
    classical
    let state : sector := ⟨nativeWord D frame beta (powers.val, {3}),
      nativeWord_sector D frame beta _, by
        simpa only [native_up_level, powers.property.2.2] using
          nativeWord_T0 D H frame leftGram rightGram beta (powers.val, {3})⟩
    refine ⟨state, state, ?_⟩
    apply Subtype.ext
    change P D frame inverse leftFrame rightFrame xAxis yAxis (nativeState D frame beta
      powers.val 1 {3}) = nativeState D frame beta powers.val 1 {3}
    rw [P_native, if_pos ((kappa_zero_iff D xAxis yAxis powers.val {3}).mpr
      ⟨powers.property.1, powers.property.2.1, Finset.Subset.refl _⟩), one_smul])

theorem upInput_state (values : coefficients) :
    (upInput D H frame inverse leftGram rightGram leftFrame rightFrame beta xAxis yAxis
      level values).val.val = upState D frame beta xAxis yAxis level values := by
  simp only [upInput, upState, Finsupp.linearCombination_apply, Finsupp.sum,
    Submodule.coe_sum, Submodule.coe_smul]

private theorem upState_degree (values : coefficients) :
    upState D frame beta xAxis yAxis level values ∈ ghostPart D 2 := by
  classical
  simp only [upState, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro powers member
  apply Submodule.smul_mem
  apply (ghostPart_iff_number D 2 _).mpr
  simpa [nativeJ, epsilonCount, thetaCount, etaCount, Finset.filter_singleton] using
    nativeWord_J D frame beta (powers.val, {3})

private theorem input_fixed (input : LinearMap.range energyP) : energyP input.val = input.val := by
  obtain ⟨preimage, equation⟩ := input.property
  rw [← equation]
  apply Subtype.ext
  simp only [energyProjector_coe]
  exact LinearMap.congr_fun (native_P_idempotent D frame inverse leftFrame rightFrame
    xAxis yAxis) preimage.val

variable (critical : D.rank = 26) (null : gramPair D nullDirection nullDirection = 0)
variable (nonzero : chosenP D beta nullDirection ≠ 0) (distinct : xAxis ≠ yAxis)
variable (xRow : frame xAxis = nullDirection)
variable (yRow : frame yAxis = adaptedPartner D beta nullDirection)
variable (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
variable (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
variable (shell : chosenH D beta + (level : ℂ) - 1 = 0)

local notation "laws" => original_energy_finite_transfer_laws D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
  xRow yRow xDual yDual
local notation "differentialZero" => absoluteEnergyDifferentialSupplier D H frame inverse
  leftGram rightGram leftFrame rightFrame beta nullDirection xAxis yAxis level null nonzero
  distinct xRow yRow xDual yDual shell
local notation "degreeCycles" => ghostCycles D H sector 2
local notation "stable" => energyStable D H leftGram rightGram beta level
local notation "degreeBoundaries" => ghostBoundaries D H leftGram rightGram critical sector stable 2
local notation "degreeCohomology" => ghostCohomology D H leftGram rightGram critical sector stable 2
local notation "nativeInput" => upInput D H frame inverse leftGram rightGram leftFrame rightFrame
  beta xAxis yAxis level

include critical null nonzero distinct xRow yRow xDual yDual shell in
def upLift : coefficients →ₗ[ℂ] degreeCycles where
  toFun values := by
    let included := energyI (nativeInput values).val
    have chain := LinearMap.congr_fun laws.1 (nativeInput values).val
    have cycle : energyQ included = 0 := by
      simpa only [Module.End.mul_apply, differentialZero, LinearMap.zero_apply,
        map_zero] using chain
    refine ⟨included.val, ⟨⟨included.property, congrArg Subtype.val cycle⟩, ?_⟩⟩
    apply energyInclusion_ghost D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level 2
    rw [upInput_state]
    exact upState_degree D frame beta xAxis yAxis level values
  map_add' := by intro first second; apply Subtype.ext; simp
  map_smul' := by intro scalar values; apply Subtype.ext; simp

local notation "lift" => upLift D H frame inverse leftGram rightGram leftFrame rightFrame
  beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell

def upReadout : degreeCycles →ₗ[ℂ] coefficients :=
  (upCoordinates D frame inverse leftFrame rightFrame beta xAxis yAxis level).comp
    ((sector).subtype.comp ((energyR).comp ((degreeCycles).subtype.codRestrict sector
      (fun state => state.property.1.1))))

local notation "readout" => upReadout D H frame inverse leftGram rightGram leftFrame rightFrame
  beta nullDirection xAxis yAxis level

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem upReadout_lift (values : coefficients) : readout (lift values) = values := by
  have retract := LinearMap.congr_fun laws.2.2.1 (nativeInput values).val
  have equation : energyR (energyI (nativeInput values).val) = (nativeInput values).val := by
    simpa only [Module.End.mul_apply, input_fixed] using retract
  change upCoordinates D frame inverse leftFrame rightFrame beta xAxis yAxis level
    (energyR (energyI (nativeInput values).val)).val = values
  rw [equation, upInput_state]
  exact upCoordinates_upState D frame inverse leftFrame rightFrame beta xAxis yAxis level values

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem upReadout_boundary (state : degreeCycles) (boundary : state ∈ degreeBoundaries) :
    readout state = 0 := by
  obtain ⟨preimage, equation⟩ := (ghostBoundary_iff D H leftGram rightGram critical
    sector stable 2 state).mp boundary
  let input : sector := ⟨state.val, state.property.1.1⟩
  let preceding : sector := ⟨preimage.val, preimage.property.1⟩
  have energyEquation : energyQ preceding = input := Subtype.ext equation
  have chain := LinearMap.congr_fun laws.2.1 preceding
  have zero : energyR input = 0 := by
    simpa only [Module.End.mul_apply, energyEquation, differentialZero,
      LinearMap.zero_apply] using chain
  change upCoordinates D frame inverse leftFrame rightFrame beta xAxis yAxis level
    (energyR input).val = 0
  rw [zero, Submodule.coe_zero, map_zero]

include critical null nonzero distinct xRow yRow xDual yDual shell in
def upQuotientProjection : degreeCohomology →ₗ[ℂ] coefficients :=
  (degreeBoundaries).liftQ readout (by
    intro state boundary
    exact upReadout_boundary D H frame inverse leftGram rightGram leftFrame rightFrame beta
      nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual
      shell state boundary)

include critical null nonzero distinct xRow yRow xDual yDual shell in
def upQuotientClass : coefficients →ₗ[ℂ] degreeCohomology :=
  (degreeBoundaries).mkQ.comp lift

local notation "projection" => upQuotientProjection D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
  xRow yRow xDual yDual shell
local notation "classMap" => upQuotientClass D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
  xRow yRow xDual yDual shell

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem upQuotient_left_inverse (values : coefficients) : projection (classMap values) = values :=
  upReadout_lift D H frame inverse leftGram rightGram leftFrame rightFrame beta nullDirection
    xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell values

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem upQuotient_right_inverse (quotient : degreeCohomology) : classMap (projection quotient) =
    quotient := by
  obtain ⟨state, rfl⟩ := (degreeBoundaries).mkQ_surjective quotient
  let input : sector := ⟨state.val, state.property.1.1⟩
  have projectedDegree := energyProjection_ghost D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis level 2 input state.property.2
  have recovery := upState_coordinates D H frame inverse leftGram rightGram leftFrame rightFrame
    beta xAxis yAxis level (energyR input)
    (energyProjection_fixed D H frame inverse leftGram rightGram leftFrame rightFrame beta
      nullDirection xAxis yAxis level input) projectedDegree
  have inputRecovery : (nativeInput (readout state)).val = energyR input := by
    apply Subtype.ext
    rw [upInput_state]
    exact recovery
  have liftRecovery : (lift (readout state)).val = (energyI (energyR input)).val := by
    change (energyI (nativeInput (readout state)).val).val = _
    rw [inputRecovery]
  have boundary := cycle_homotopy_boundary D H frame inverse leftGram rightGram leftFrame
    rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
    xRow yRow xDual yDual input state.property.1.2
  change (degreeBoundaries).mkQ (lift (readout state)) = (degreeBoundaries).mkQ state
  apply (Submodule.Quotient.eq _).mpr
  apply (ghostBoundary_iff D H leftGram rightGram critical sector stable 2 _).mpr
  refine ⟨⟨-(energyHomotopy input).val, (-(energyHomotopy input)).property, ?_⟩, ?_⟩
  · apply (ghostPart D (2 - 1)).neg_mem
    exact energyHomotopy_ghost D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level 2 input state.property.2
  · change Q D H (-(energyHomotopy input).val) = (lift (readout state)).val - state.val
    rw [map_neg, liftRecovery, ← boundary]
    exact neg_sub _ _

include critical null nonzero distinct xRow yRow xDual yDual shell in
def nativeUpEquiv : coefficients ≃ₗ[ℂ] degreeCohomology where
  toLinearMap := classMap
  invFun := projection
  left_inv := upQuotient_left_inverse D H frame inverse leftGram rightGram leftFrame rightFrame
    beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell
  right_inv := upQuotient_right_inverse D H frame inverse leftGram rightGram leftFrame rightFrame
    beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell

#print axioms upState_coordinates
#print axioms upLift
#print axioms nativeUpEquiv

end
end D5.S3.VertexAlgebra.OriginalAbsoluteGhostDoublet
