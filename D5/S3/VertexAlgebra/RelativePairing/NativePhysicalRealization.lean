/- GID: D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization
   generality: I
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite HPL realization of transverse down coefficients in the literal physical image. -/

import D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates
import D5.S3.VertexAlgebra.RelativePairing.OriginalPhysicalDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  LatticeBcGhostNeutralCohomology LatticeBcGhostBrstGhostNumber
  OriginalQQuartetSource OriginalQEnergyInclusionPairing OriginalBrstReassembly
  OriginalQPhysicalPairing NativeTransverseCoordinates
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData) (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
variable (leftFrame : inverse * frame = 1) (rightFrame : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank) (level : ℤ)
variable (critical : D.rank = 26) (null : gramPair D nullDirection nullDirection = 0)
variable (nonzero : chosenP D beta nullDirection ≠ 0) (distinct : xAxis ≠ yAxis)
variable (xRow : frame xAxis = nullDirection)
variable (yRow : frame yAxis = adaptedPartner D beta nullDirection)
variable (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
variable (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
variable (shell : chosenH D beta + (level : ℂ) - 1 = 0)

local notation "sector" => originalEnergySector D H beta level
local notation "energyQ" => energyOriginalQ D H leftGram rightGram beta level
local notation "energyP" => energyProjector D H frame inverse leftGram rightGram
  leftFrame rightFrame beta xAxis yAxis level
local notation "energyI" => energyTransferInclusion D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyR" => energyTransferProjection D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyHomotopy" => energyTransferHomotopy D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "energyDiff" => energyTransferredDifferential D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "inc" => energyReducedInclusion D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "proj" => energyReducedProjection D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level
local notation "nativeCoordinates" => NativeTransverseCoordinates.coordinates D frame inverse leftFrame rightFrame
  beta xAxis yAxis level
local notation "nativeDown" => downState D frame beta xAxis yAxis level
local notation "laws" => original_energy_finite_transfer_laws D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
  xRow yRow xDual yDual
local notation "antighostLaws" => energy_B0_transfer_compatibility_on_shell D H frame inverse
  leftGram rightGram leftFrame rightFrame beta nullDirection xAxis yAxis level
  xDual yDual nonzero shell

def inputMap : (TransverseDownIndex D xAxis yAxis level →₀ ℂ) →ₗ[ℂ] LinearMap.range energyP :=
  Finsupp.linearCombination ℂ (fun powers => energyTransverseDownInput D H frame inverse
    leftGram rightGram leftFrame rightFrame xAxis yAxis beta level powers.val
    powers.property.1 powers.property.2.1 powers.property.2.2)

local notation "nativeInput" => inputMap D H frame inverse leftGram rightGram leftFrame rightFrame
  beta xAxis yAxis level

private theorem input_state (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    (nativeInput coefficients).val.val = nativeDown coefficients :=
  energyInput_state D H frame inverse leftGram rightGram leftFrame rightFrame
    beta xAxis yAxis level coefficients

private theorem input_fixed (input : LinearMap.range energyP) : energyP input.val = input.val := by
  obtain ⟨state, equality⟩ := input.property
  apply Subtype.ext
  change P D frame inverse leftFrame rightFrame xAxis yAxis input.val.val = input.val.val
  rw [← equality]
  exact LinearMap.congr_fun
    (native_P_idempotent D frame inverse leftFrame rightFrame xAxis yAxis) state.val

include null nonzero distinct xRow yRow xDual yDual shell in
private theorem differential_zero : energyDiff = 0 := by
  apply LinearMap.ext
  intro input
  apply Subtype.ext
  have massShell := original_transferred_differential_mass_shell D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis null nonzero distinct
    xRow yRow xDual yDual level input.val input.property.1 input.property.2
  simpa only [energyTransferredDifferential_coe, shell, zero_smul,
    LinearMap.zero_apply, Submodule.coe_zero] using massShell

private theorem down_degree (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    nativeDown coefficients ∈ ghostPart D 1 := by
  apply (ghostPart_iff_number D 1 _).mpr
  rw [downState_tensor]
  simp [nativeJ, LatticeBcGhostBrstGhostNumber.J, TensorProduct.map_tmul,
    OriginalQQuartetSource.down_original_basis, BcGhostNumber.J, BcGhostNumber.degree,
    Finset.filter_insert, Finset.filter_singleton]

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem inclusion_physical (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    let included := inc (nativeInput coefficients)
    Q D H included.val = 0 ∧ B D 0 included.val = 0 ∧ included.val ∈ ghostPart D 1 := by
  dsimp only
  let input := nativeInput coefficients
  have inputState : input.val.val = nativeDown coefficients :=
    energyInput_state D H frame inverse leftGram rightGram leftFrame rightFrame
      beta xAxis yAxis level coefficients
  have inputB : energyB0 D H beta level input.val = 0 := by
    apply Subtype.ext
    change B D 0 input.val.val = 0
    rw [inputState]
    simp [downState, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, nativeWord_Bzero]
  have cycle : energyQ (inc input) = 0 := by
    change energyQ (energyI input.val) = 0
    have chain := LinearMap.congr_fun laws.1 input.val
    simpa only [Module.End.mul_apply, differential_zero D H frame inverse leftGram rightGram
      leftFrame rightFrame beta nullDirection xAxis yAxis level null nonzero distinct
      xRow yRow xDual yDual shell, LinearMap.zero_apply, map_zero] using chain
  have relative : energyB0 D H beta level (inc input) = 0 := by
    change energyB0 D H beta level (energyI input.val) = 0
    have compatibility := LinearMap.congr_fun antighostLaws.2.1 input.val
    simpa only [Module.End.mul_apply, inputB, map_zero] using compatibility
  refine ⟨congrArg Subtype.val cycle, congrArg Subtype.val relative, ?_⟩
  have inputDegree := (ghostPart_iff_number D 1 _).mp
    (down_degree D frame beta xAxis yAxis level coefficients)
  change LatticeBcGhostBrstGhostNumber.J D (nativeDown coefficients) =
    ((1 : ℤ) : ℂ) • nativeDown coefficients at inputDegree
  have nativeIncluded : (inc input).val =
      finiteOriginalCorrectionInverse D H frame inverse leftFrame rightFrame
        beta nullDirection xAxis yAxis level input.val.val := by
    change (energyI input.val).val = _
    simp only [energyTransferInclusion, Module.End.mul_apply, input_fixed,
      energyCorrectionInverse_coe]
  have commute := LinearMap.congr_fun
    (J0_finite_correction_inverse_commutator D H frame inverse leftFrame rightFrame
      beta nullDirection xAxis yAxis level) input.val.val
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at commute
  apply (ghostPart_iff_number D 1 _).mpr
  change LatticeBcGhostBrstGhostNumber.J D (inc input).val = ((1 : ℤ) : ℂ) • (inc input).val
  rw [nativeIncluded, sub_eq_zero.mp commute, inputState, inputDegree, map_smul]

include critical null nonzero distinct xRow yRow xDual yDual shell in
def physicalLift : (TransverseDownIndex D xAxis yAxis level →₀ ℂ) →ₗ[ℂ]
    physicalCycles D H beta level where
  toFun coefficients :=
    let included := inc (nativeInput coefficients)
    let membership := inclusion_physical D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level critical null nonzero distinct
      xRow yRow xDual yDual shell coefficients
    ⟨⟨included.val, membership.1⟩, ⟨⟨included.property, membership.2.1⟩, membership.2.2⟩⟩
  map_add' := by intro first second; apply Subtype.ext; apply Subtype.ext; simp
  map_smul' := by intro scalar coefficients; apply Subtype.ext; apply Subtype.ext; simp

local notation "lift" => physicalLift D H frame inverse leftGram rightGram leftFrame rightFrame
  beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell

include critical null nonzero distinct xRow yRow xDual yDual shell in
def nativeImage : (TransverseDownIndex D xAxis yAxis level →₀ ℂ) →ₗ[ℂ]
    physicalImage D H beta level := (imageRepresentative D H beta level).comp lift

local notation "realization" => nativeImage D H frame inverse leftGram rightGram leftFrame rightFrame
  beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem nativeImage_originalClass (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    (realization coefficients).val = (OriginalBoundaries D H).mkQ (lift coefficients).val := rfl

def physicalEnergyMap : physicalCycles D H beta level →ₗ[ℂ] sector :=
  (physicalState D H beta level).codRestrict sector (fun state => state.property.1.1)

local notation "physicalEnergy" => physicalEnergyMap D H beta level

def physicalProjection : physicalCycles D H beta level →ₗ[ℂ]
    TransverseDownIndex D xAxis yAxis level →₀ ℂ :=
  (nativeCoordinates).comp (((sector).subtype).comp ((energyR).comp physicalEnergy))

local notation "physicalCoordinates" => physicalProjection D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level

include nonzero xDual yDual shell in
theorem projection_relative (state : physicalCycles D H beta level) :
    B D 0 (energyR (physicalEnergy state)).val = 0 := by
  have inputB : energyB0 D H beta level (physicalEnergy state) = 0 := by
    apply Subtype.ext
    exact state.property.1.2
  have compatibility := LinearMap.congr_fun antighostLaws.2.2 (physicalEnergy state)
  have zero : energyB0 D H beta level (energyR (physicalEnergy state)) = 0 := by
    simpa only [Module.End.mul_apply, inputB, map_zero] using compatibility
  exact congrArg Subtype.val zero

include nonzero xDual yDual shell in
theorem projection_coordinate_recovery (state : physicalCycles D H beta level) :
    nativeDown (physicalCoordinates state) = (energyR (physicalEnergy state)).val := by
  apply downState_coordinates D H frame inverse leftGram rightGram leftFrame rightFrame
    beta xAxis yAxis level (energyR (physicalEnergy state))
  · exact congrArg Subtype.val (input_fixed D H frame inverse leftGram rightGram leftFrame rightFrame
      beta xAxis yAxis level (proj (physicalEnergy state)))
  · exact projection_relative D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level nonzero xDual yDual shell state

include nonzero xDual yDual shell in
theorem projection_ghost_one (state : physicalCycles D H beta level) :
    (energyR (physicalEnergy state)).val ∈ ghostPart D 1 := by
  rw [← projection_coordinate_recovery D H frame inverse leftGram rightGram leftFrame rightFrame
    beta nullDirection xAxis yAxis level nonzero xDual yDual shell state]
  exact down_degree D frame beta xAxis yAxis level _

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem physicalProjection_lift (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    physicalCoordinates (lift coefficients) = coefficients := by
  have retract := LinearMap.congr_fun laws.2.2.1 (nativeInput coefficients).val
  have recovered : energyR (inc (nativeInput coefficients)) = (nativeInput coefficients).val := by
    change energyR (energyI (nativeInput coefficients).val) = (nativeInput coefficients).val
    simpa only [Module.End.mul_apply, input_fixed] using retract
  change nativeCoordinates (energyR (inc (nativeInput coefficients))).val = coefficients
  rw [recovered, input_state]
  exact coordinates_downState D frame inverse leftFrame rightFrame beta xAxis yAxis level coefficients

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem physicalProjection_boundary (state : physicalCycles D H beta level)
    (boundary : state ∈ physicalBoundaries D H beta level) : physicalCoordinates state = 0 := by
  obtain ⟨preimage, equation⟩ :=
    (ambient_boundary_sector_preimage D H leftGram rightGram beta level (physicalEnergy state)).mp boundary
  have chain := LinearMap.congr_fun laws.2.1 preimage
  have zero : energyR (physicalEnergy state) = 0 := by
    simpa only [Module.End.mul_apply, equation,
      differential_zero D H frame inverse leftGram rightGram leftFrame rightFrame
        beta nullDirection xAxis yAxis level null nonzero distinct xRow yRow xDual yDual shell,
      LinearMap.zero_apply] using chain
  change nativeCoordinates (energyR (physicalEnergy state)).val = 0
  simp only [zero, Submodule.coe_zero, map_zero]

include critical null nonzero distinct xRow yRow xDual yDual shell in
private theorem quotient_projection_kernel :
    physicalBoundaries D H beta level ≤ LinearMap.ker physicalCoordinates := by
  intro state boundary
  change physicalCoordinates state = 0
  exact physicalProjection_boundary D H frame inverse leftGram rightGram leftFrame rightFrame
    beta nullDirection xAxis yAxis level critical null nonzero distinct
    xRow yRow xDual yDual shell state boundary

private def quotientLinearMap {Carrier Readout : Type*}
    [AddCommGroup Carrier] [Module ℂ Carrier] [AddCommGroup Readout] [Module ℂ Readout]
    (boundaries : Submodule ℂ Carrier) (readout : Carrier →ₗ[ℂ] Readout)
    (vanishing : boundaries ≤ LinearMap.ker readout) : Carrier ⧸ boundaries →ₗ[ℂ] Readout :=
  boundaries.liftQ readout vanishing

include critical null nonzero distinct xRow yRow xDual yDual shell in
def quotientProjection : PhysicalCohomology D H beta level →ₗ[ℂ]
    (TransverseDownIndex D xAxis yAxis level →₀ ℂ) :=
  @quotientLinearMap (physicalCycles D H beta level)
    (TransverseDownIndex D xAxis yAxis level →₀ ℂ)
    inferInstance inferInstance inferInstance inferInstance
    (physicalBoundaries D H beta level) physicalCoordinates
    (quotient_projection_kernel D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell)

local notation "quotientCoordinates" => quotientProjection D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
  xRow yRow xDual yDual shell

include critical null nonzero distinct xRow yRow xDual yDual shell in
def imageProjection : physicalImage D H beta level →ₗ[ℂ]
    TransverseDownIndex D xAxis yAxis level →₀ ℂ :=
  (quotientCoordinates).comp (imageEquiv D H beta level).symm.toLinearMap

local notation "extraction" => imageProjection D H frame inverse leftGram rightGram leftFrame rightFrame
  beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell

include critical null nonzero distinct xRow yRow xDual yDual shell in
set_option backward.isDefEq.respectTransparency true in
theorem imageProjection_representative (state : physicalCycles D H beta level) :
    extraction (imageRepresentative D H beta level state) = physicalCoordinates state := by
  have represented : imageRepresentative D H beta level state =
      (imageEquiv D H beta level)
        (Submodule.Quotient.mk state : PhysicalCohomology D H beta level) := by
    apply Subtype.ext
    rfl
  rw [represented]
  simp only [imageProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem imageProjection_nativeImage (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    extraction (realization coefficients) = coefficients := by
  rw [show realization coefficients = imageRepresentative D H beta level (lift coefficients) from rfl,
    imageProjection_representative]
  exact physicalProjection_lift D H frame inverse leftGram rightGram leftFrame rightFrame
    beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell _

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem nativeImage_representative (state : physicalCycles D H beta level) :
    realization (physicalCoordinates state) = imageRepresentative D H beta level state := by
  have recovered : (nativeInput (physicalCoordinates state)).val = energyR (physicalEnergy state) := by
    apply Subtype.ext
    rw [input_state]
    exact projection_coordinate_recovery D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level nonzero xDual yDual shell state
  have cycle : energyQ (physicalEnergy state) = 0 := by
    apply Subtype.ext
    exact state.val.property
  have contraction := LinearMap.congr_fun laws.2.2.2.1 (physicalEnergy state)
  have boundaryEquation : energyQ (energyHomotopy (physicalEnergy state)) =
      physicalEnergy state - energyI (energyR (physicalEnergy state)) := by
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.one_apply, cycle, map_zero, add_zero] using contraction
  apply Subtype.ext
  rw [nativeImage_originalClass]
  change (OriginalBoundaries D H).mkQ (lift (physicalCoordinates state)).val =
    (OriginalBoundaries D H).mkQ state.val
  apply (Submodule.Quotient.eq (OriginalBoundaries D H)).mpr
  refine ⟨-(energyHomotopy (physicalEnergy state)).val, ?_⟩
  change Q D H (-(energyHomotopy (physicalEnergy state)).val) =
    (inc (nativeInput (physicalCoordinates state))).val - state.val.val
  change Q D H (-(energyHomotopy (physicalEnergy state)).val) =
    (energyI (nativeInput (physicalCoordinates state)).val).val - state.val.val
  rw [map_neg, recovered]
  have ambientEquation := congrArg Subtype.val boundaryEquation
  change Q D H (energyHomotopy (physicalEnergy state)).val =
    state.val.val - (energyI (energyR (physicalEnergy state))).val at ambientEquation
  rw [ambientEquation]
  abel

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem nativeImage_imageProjection (state : physicalImage D H beta level) :
    realization (extraction state) = state := by
  obtain ⟨quotient, equality⟩ := state.property
  induction quotient using Submodule.Quotient.induction_on with
  | _ representative =>
    have represented : state = imageRepresentative D H beta level representative := by
      apply Subtype.ext
      exact equality.symm
    rw [represented, imageProjection_representative]
    exact nativeImage_representative D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell _

include critical null nonzero distinct xRow yRow xDual yDual shell in
def nativePhysicalEquiv : (TransverseDownIndex D xAxis yAxis level →₀ ℂ) ≃ₗ[ℂ]
    physicalImage D H beta level where
  toLinearMap := realization
  invFun := extraction
  left_inv := imageProjection_nativeImage D H frame inverse leftGram rightGram leftFrame rightFrame
    beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell
  right_inv := nativeImage_imageProjection D H frame inverse leftGram rightGram leftFrame rightFrame
    beta nullDirection xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell

include critical null nonzero distinct xRow yRow xDual yDual shell in
theorem nativeImage_form
    (xReal : ∀ axis, star (frame xAxis axis) = frame xAxis axis)
    (yReal : ∀ axis, star (frame yAxis axis) = frame yAxis axis)
    (first second : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    imageForm D H beta level frame inverse leftGram rightGram leftFrame rightFrame
      nullDirection xAxis yAxis critical null nonzero distinct xRow yRow xDual yDual shell
      (realization first) (realization second) =
        -LatticeOscillatorFockForm.fockForm D
          (transverseDownOscillator D frame xAxis yAxis level first)
          (transverseDownOscillator D frame xAxis yAxis level second) := by
  rw [show realization first = imageRepresentative D H beta level (lift first) from rfl,
    show realization second = imageRepresentative D H beta level (lift second) from rfl,
    imageForm_recovery]
  change LatticeBcGhostHermitianForm.F D (inc (nativeInput first)).val
    (C D 0 (inc (nativeInput second)).val) = _
  simpa only [inputMap, energyTransverseDownCombination, if_true] using
    energyReducedInclusion_transverse_down_normalization
    D H frame inverse leftGram rightGram leftFrame rightFrame nullDirection xAxis yAxis
    null distinct xRow xReal yReal xDual yDual beta beta level level nonzero nonzero
    yRow yRow first second

#print axioms nativePhysicalEquiv
#print axioms nativeImage_form

end
end D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization
