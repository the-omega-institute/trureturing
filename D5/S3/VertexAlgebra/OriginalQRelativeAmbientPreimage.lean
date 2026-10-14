/- GID: D5/S3/VertexAlgebra/OriginalQRelativeAmbientPreimage
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous native relative preimages and literal physical quotient equality on shell. -/

import D5.S3.VertexAlgebra.OriginalQRelativeFiniteHpl
import D5.S3.VertexAlgebra.OriginalNonzeroGhostTransferJ
import D5.S3.VertexAlgebra.OriginalQLiteralQuotientTransient
import D5.S3.VertexAlgebra.OriginalIntegralGhostCohomologyTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge LatticeBcGhostBrstGhostNumber OriginalBrstReassembly
open scoped BigOperators

noncomputable section

variable (D : LatticeData)
  (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
  (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
  (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
  (xAxis yAxis : Fin D.rank) (level : ℤ)

local notation "energyQ" => energyOriginalQ D H leftGramInverse rightGramInverse beta level
local notation "energyHomotopy" => energyTransferHomotopy D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyProjection" => energyTransferProjection D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "energyDifferential" => energyTransferredDifferential D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "normalizer" => S D frame inverse leftFrameInverse rightFrameInverse
  xAxis yAxis (chosenP D beta nullDirection)
local notation "correctionInverse" => finiteOriginalCorrectionInverse D H frame inverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level

private theorem native_transfer_homotopy_ghost_degree (degree : ℤ)
    (state : originalEnergySector D H beta level) (homogeneous : state.val ∈ ghostPart D degree) :
    (energyHomotopy state).val ∈ ghostPart D (degree - 1) := by
  have number := (ghostPart_iff_number D degree state.val).mp homogeneous
  change J D state.val = (degree : ℂ) • state.val at number
  have normalizerNumber := LinearMap.congr_fun
    (J0_S_commutator D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis (chosenP D beta nullDirection)) state.val
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply] at normalizerNumber
  have normalizedDegree : J D (normalizer state.val) = ((degree - 1 : ℤ) : ℂ) • normalizer state.val := by
    calc
      _ = -normalizer state.val + normalizer (J D state.val) :=
        sub_eq_iff_eq_add.mp normalizerNumber
      _ = -normalizer state.val + (degree : ℂ) • normalizer state.val := by rw [number, map_smul]
      _ = _ := by simp only [Int.cast_sub, Int.cast_one, sub_smul, one_smul]; abel
  have inverseNumber := LinearMap.congr_fun
    (J0_finite_correction_inverse_commutator D H frame inverse leftFrameInverse rightFrameInverse
      beta nullDirection xAxis yAxis level) (normalizer state.val)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at inverseNumber
  have nativeHomotopy : (energyHomotopy state).val = correctionInverse (normalizer state.val) := by
    simp only [energyTransferHomotopy, Module.End.mul_apply, energyCorrectionInverse_coe,
      energyNormalizer_coe]
  apply (ghostPart_iff_number D (degree - 1) _).mpr
  change J D (energyHomotopy state).val = ((degree - 1 : ℤ) : ℂ) • (energyHomotopy state).val
  rw [nativeHomotopy, sub_eq_zero.mp inverseNumber, normalizedDegree, map_smul]

theorem relative_ambient_boundary_homotopy_preimage
    (critical : D.rank = 26)
    (null : gramPair D nullDirection nullDirection = 0)
    (nonzero : chosenP D beta nullDirection ≠ 0) (distinct : xAxis ≠ yAxis)
    (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (shell : chosenH D beta + (level : ℂ) - 1 = 0)
    (degree : ℤ) (state : originalEnergySector D H beta level)
    (relative : B D 0 state.val = 0) (cycle : Q D H state.val = 0)
    (homogeneous : state.val ∈ ghostPart D degree)
    (ambientBoundary : ∃ preimage : State D, Q D H preimage = state.val) :
    let preimage := energyHomotopy state
    B D 0 preimage.val = 0 ∧ preimage.val ∈ ghostPart D (degree - 1) ∧
      Q D H preimage.val = state.val := by
  dsimp only
  have laws := original_energy_finite_transfer_laws D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
    xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual
  have differentialZero : energyDifferential = 0 := by
    apply LinearMap.ext
    intro input
    apply Subtype.ext
    have massShell := original_transferred_differential_mass_shell D H frame inverse
      leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
      xAxis yAxis null nonzero distinct xRow yRow xDual yDual level input.val
      input.property.1 input.property.2
    simpa only [energyTransferredDifferential_coe, shell, zero_smul,
      LinearMap.zero_apply, Submodule.coe_zero] using massShell
  obtain ⟨sectorPreimage, sectorEquation⟩ :=
    (ambient_boundary_sector_preimage D H leftGramInverse rightGramInverse beta level state).mp ambientBoundary
  have projectionZero : energyProjection state = 0 := by
    have chain := LinearMap.congr_fun laws.2.1 sectorPreimage
    simpa only [Module.End.mul_apply, sectorEquation, differentialZero, LinearMap.zero_apply] using chain
  have cycleZero : energyQ state = 0 := by
    apply Subtype.ext
    simpa only [energyOriginalQ_coe, Submodule.coe_zero] using cycle
  have preimageEquation : energyQ (energyHomotopy state) = state := by
    have contraction := LinearMap.congr_fun laws.2.2.2.1 state
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.one_apply, cycleZero, projectionZero, map_zero, add_zero, sub_zero] using contraction
  have antighostZero : energyB0 D H beta level state = 0 := by
    apply Subtype.ext
    simpa only [energyB0_coe, Submodule.coe_zero] using relative
  have relativePreimage : energyB0 D H beta level (energyHomotopy state) = 0 := by
    have compatibility := (energy_B0_transfer_compatibility_on_shell D H frame inverse
      leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
      xAxis yAxis level xDual yDual nonzero shell).1
    have applied := LinearMap.congr_fun compatibility state
    simpa only [LinearMap.add_apply, Module.End.mul_apply, antighostZero,
      map_zero, zero_add, LinearMap.zero_apply] using applied
  refine ⟨?_, native_transfer_homotopy_ghost_degree D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
    xAxis yAxis level degree state homogeneous, ?_⟩
  · simpa only [energyB0_coe, Submodule.coe_zero] using congrArg Subtype.val relativePreimage
  · simpa only [energyOriginalQ_coe] using congrArg Subtype.val preimageEquation

include leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse in
theorem literal_physical_equality_iff_relative_preimage
    (critical : D.rank = 26)
    (null : gramPair D nullDirection nullDirection = 0)
    (nonzero : chosenP D beta nullDirection ≠ 0) (distinct : xAxis ≠ yAxis)
    (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (shell : chosenH D beta + (level : ℂ) - 1 = 0)
    (first second : originalEnergySector D H beta level)
    (firstCycle : Q D H first.val = 0) (secondCycle : Q D H second.val = 0)
    (firstRelative : B D 0 first.val = 0) (secondRelative : B D 0 second.val = 0)
    (firstDegree : first.val ∈ ghostPart D 1) (secondDegree : second.val ∈ ghostPart D 1) :
    ((LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
        (⟨first.val, firstCycle⟩ : LatticeBcGhostNeutralCohomology.OriginalCycles D H) =
      (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H).mkQ
        (⟨second.val, secondCycle⟩ : LatticeBcGhostNeutralCohomology.OriginalCycles D H)) ↔
      ∃ preimage : originalEnergySector D H beta level,
        B D 0 preimage.val = 0 ∧ preimage.val ∈ ghostPart D 0 ∧
          Q D H preimage.val = first.val - second.val := by
  constructor
  · intro equality
    have member := (Submodule.Quotient.eq
      (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H)).mp equality
    change ∃ preimage : State D, Q D H preimage = first.val - second.val at member
    have relativeDifference : B D 0 (first - second).val = 0 := by
      simp only [Submodule.coe_sub, map_sub, firstRelative, secondRelative, sub_self]
    have cycleDifference : Q D H (first - second).val = 0 := by
      simp only [Submodule.coe_sub, map_sub, firstCycle, secondCycle, sub_self]
    have repaired := relative_ambient_boundary_homotopy_preimage D H frame inverse
      leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
      xAxis yAxis level critical null nonzero distinct xRow yRow xDual yDual shell 1
      (first - second) relativeDifference cycleDifference
      ((ghostPart D 1).sub_mem firstDegree secondDegree) member
    refine ⟨energyHomotopy (first - second), repaired.1, ?_, repaired.2.2⟩
    simpa only [sub_self] using repaired.2.1
  · rintro ⟨preimage, _relative, _homogeneous, equation⟩
    apply (Submodule.Quotient.eq
      (LatticeBcGhostNeutralCohomology.OriginalBoundaries D H)).mpr
    change ∃ witness : State D, Q D H witness = first.val - second.val
    exact ⟨preimage.val, equation⟩

#print axioms relative_ambient_boundary_homotopy_preimage
#print axioms literal_physical_equality_iff_relative_preimage

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
