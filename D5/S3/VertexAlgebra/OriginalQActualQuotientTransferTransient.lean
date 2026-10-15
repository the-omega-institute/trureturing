import D5.S3.VertexAlgebra.OriginalQTrueQuotientTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open OriginalQFiniteHplCheck

noncomputable section

variable (D : LatticeData)
variable (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank) (level : ℤ)

local notation "energyQ" => energyOriginalQ D H leftGramInverse rightGramInverse beta level
local notation "energyDelta" => energyLeading D H leftGramInverse rightGramInverse beta nullDirection level
local notation "energyS" => energyNormalizer D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyP" => energyProjector D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta xAxis yAxis level
local notation "energyInverse" => energyCorrectionInverse D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyInclusion" => energyTransferInclusion D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyHomotopy" => energyTransferHomotopy D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyProjection" => energyTransferProjection D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyDifferential" => energyTransferredDifferential D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level

def energyReducedDifferential : Module.End ℂ (LinearMap.range energyP) :=
  LinearMap.restrict energyDifferential (by
    intro state member
    refine ⟨(energyQ - energyDelta) (energyInverse (energyP state)), ?_⟩
    rfl)

def energyReducedInclusion : LinearMap.range energyP →ₗ[ℂ] originalEnergySector D H beta level :=
  LinearMap.domRestrict energyInclusion (LinearMap.range energyP)

def energyReducedProjection : originalEnergySector D H beta level →ₗ[ℂ] LinearMap.range energyP :=
  LinearMap.codRestrict (LinearMap.range energyP) energyProjection (by
    intro state
    refine ⟨(1 - (energyQ - energyDelta) * (energyInverse * energyS)) state, ?_⟩
    rfl)

local notation "reducedDifferential" => energyReducedDifferential D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "reducedInclusion" => energyReducedInclusion D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "reducedProjection" => energyReducedProjection D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem original_energy_true_quotient_transfer
    (critical : D.rank = 26)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    ∃ (originalSquare : energyQ * energyQ = 0)
      (reducedSquare : reducedDifferential * reducedDifferential = 0),
      Nonempty (trueCohomology (Source := LinearMap.range energyP) reducedDifferential reducedSquare ≃ₗ[ℂ]
        trueCohomology (Source := originalEnergySector D H beta level) energyQ originalSquare) := by
  have laws := original_energy_finite_transfer_laws D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level critical null nonzero
    distinct xRow yRow xDual yDual
  have originalSquare : energyQ * energyQ = 0 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    simpa only [Module.End.mul_apply, energyOriginalQ_coe, LinearMap.zero_apply, Submodule.coe_zero]
      using LinearMap.congr_fun
        (LatticeBcGhostBrstNilpotence.nilpotent D H leftGramInverse rightGramInverse critical) state.val
  have reducedSquare : reducedDifferential * reducedDifferential = 0 := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    change energyDifferential (energyDifferential state.val) = 0
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun laws.2.2.2.2 state.val
  have inclusionChain : LinearMap.comp energyQ reducedInclusion = LinearMap.comp reducedInclusion reducedDifferential := by
    apply LinearMap.ext
    intro state
    change energyQ (energyInclusion state.val) = energyInclusion (energyDifferential state.val)
    exact LinearMap.congr_fun laws.1 state.val
  have projectionChain : LinearMap.comp reducedDifferential reducedProjection = LinearMap.comp reducedProjection energyQ := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    change energyDifferential (energyProjection state) = energyProjection (energyQ state)
    exact (LinearMap.congr_fun laws.2.1 state).symm
  have retract : LinearMap.comp reducedProjection reducedInclusion = LinearMap.id := by
    apply LinearMap.ext
    intro state
    apply Subtype.ext
    change energyProjection (energyInclusion state.val) = state.val
    calc
      _ = energyP state.val := LinearMap.congr_fun laws.2.2.1 state.val
      _ = state.val := by
        obtain ⟨preimage, equality⟩ := state.property
        rw [← equality]
        have pSquare : energyP * energyP = energyP := by
          apply LinearMap.ext
          intro originalState
          apply Subtype.ext
          simpa only [Module.End.mul_apply, energyProjector_coe] using LinearMap.congr_fun
            (native_P_idempotent D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis)
              originalState.val
        exact LinearMap.congr_fun pSquare preimage
  exact ⟨originalSquare, reducedSquare, @true_quotient_equivalence
    (originalEnergySector D H beta level) (LinearMap.range energyP)
    inferInstance inferInstance inferInstance inferInstance energyQ reducedDifferential
    originalSquare reducedSquare reducedInclusion reducedProjection energyHomotopy
    inclusionChain projectionChain retract (by
      apply LinearMap.ext
      intro state
      change (energyQ * energyHomotopy + energyHomotopy * energyQ) state =
        (1 - energyInclusion * energyProjection) state
      exact LinearMap.congr_fun laws.2.2.2.1 state)⟩

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
