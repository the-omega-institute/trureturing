/- GID: D5/S3/VertexAlgebra/OriginalQRelativeFiniteHpl
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native antighost compatibility of the finite original-Q transfer on an on-shell energy sector. -/

import D5.S3.VertexAlgebra.OriginalQAmbientEnergyProjectionTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open scoped BigOperators

private theorem finite_B0_factor_algebra {Algebra : Type*} [Ring Algebra]
    (antighost original leading normalizer projector : Algebra) (cutoff : ℕ)
    (originalAnti : original * antighost + antighost * original = 0)
    (leadingAnti : leading * antighost + antighost * leading = 0)
    (normalizerAnti : normalizer * antighost + antighost * normalizer = 0)
    (projectorCommute : antighost * projector = projector * antighost) :
    let correctionInverse := ∑ steps ∈ Finset.range cutoff,
      (-(normalizer * (original - leading))) ^ steps
    let homotopy := correctionInverse * normalizer
    antighost * correctionInverse = correctionInverse * antighost ∧
      (antighost * correctionInverse = correctionInverse * antighost →
      homotopy * antighost + antighost * homotopy = 0 ∧
      antighost * (correctionInverse * projector) = (correctionInverse * projector) * antighost ∧
      antighost * (projector * (1 - (original - leading) * homotopy)) =
        (projector * (1 - (original - leading) * homotopy)) * antighost) := by
  dsimp only
  let correctionInverse := ∑ steps ∈ Finset.range cutoff,
    (-(normalizer * (original - leading))) ^ steps
  let homotopy := correctionInverse * normalizer
  have perturbationAnti : (original - leading) * antighost + antighost * (original - leading) = 0 := by
    calc
      _ = (original * antighost + antighost * original) -
          (leading * antighost + antighost * leading) := by noncomm_ring
      _ = 0 := by rw [originalAnti, leadingAnti, sub_self]
  have normalizerSwap : antighost * normalizer = -(normalizer * antighost) :=
    eq_neg_of_add_eq_zero_right normalizerAnti
  have perturbationSwap : antighost * (original - leading) = -((original - leading) * antighost) :=
    eq_neg_of_add_eq_zero_right perturbationAnti
  have factorCommute : Commute antighost (-(normalizer * (original - leading))) := by
    change antighost * (-(normalizer * (original - leading))) =
      (-(normalizer * (original - leading))) * antighost
    calc
      _ = -(antighost * normalizer) * (original - leading) := by noncomm_ring
      _ = (normalizer * antighost) * (original - leading) := by rw [normalizerSwap, neg_neg]
      _ = -(normalizer * (original - leading)) * antighost := by
        rw [mul_assoc, perturbationSwap]
        noncomm_ring
  have inverseCommute : antighost * correctionInverse = correctionInverse * antighost := by
    dsimp only [correctionInverse]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun steps _ => (factorCommute.pow_right steps).eq)
  refine ⟨inverseCommute, ?_⟩
  intro suppliedInverseCommute
  change antighost * correctionInverse = correctionInverse * antighost at suppliedInverseCommute
  have homotopyAnti : homotopy * antighost + antighost * homotopy = 0 := by
    dsimp only [homotopy]
    calc
      _ = correctionInverse * (normalizer * antighost) +
          (antighost * correctionInverse) * normalizer := by noncomm_ring
      _ = correctionInverse * (normalizer * antighost + antighost * normalizer) := by
        rw [suppliedInverseCommute]
        noncomm_ring
      _ = 0 := by rw [normalizerAnti, mul_zero]
  refine ⟨homotopyAnti, ?_, ?_⟩
  · rw [← mul_assoc, suppliedInverseCommute, mul_assoc, projectorCommute, ← mul_assoc]
  · have homotopySwap : antighost * homotopy = -(homotopy * antighost) :=
      eq_neg_of_add_eq_zero_right homotopyAnti
    have productCommute : antighost * ((original - leading) * homotopy) =
        ((original - leading) * homotopy) * antighost := by
      rw [← mul_assoc, perturbationSwap, neg_mul, mul_assoc, homotopySwap]
      noncomm_ring
    change antighost * (projector * (1 - (original - leading) * homotopy)) =
      (projector * (1 - (original - leading) * homotopy)) * antighost
    calc
      _ = projector * (antighost - antighost * ((original - leading) * homotopy)) := by
        rw [← mul_assoc, projectorCommute, mul_assoc, mul_sub, mul_one]
      _ = projector * (antighost - ((original - leading) * homotopy) * antighost) := by
        rw [productCommute]
      _ = _ := by simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc]

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge OriginalBrstReassembly
open scoped BigOperators

noncomputable section

theorem original_B0_preserves_energy_sector (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D) (level : ℤ)
    (state : State D) (member : state ∈ originalEnergySector D H beta level) :
    B D 0 state ∈ originalEnergySector D H beta level := by
  constructor
  · have chargeLaw := LinearMap.congr_fun (chargeProjection_B D beta) state
    rw [← original_charge_projection_partition] at chargeLaw
    simpa only [LinearMap.comp_apply, member.1] using chargeLaw
  · have energyCommute : (M D H 0 + G D 0) * B D 0 = B D 0 * (M D H 0 + G D 0) := by
      have commutator := totalZero_B_commutator D H 0
      simp only [Int.cast_zero, neg_zero, zero_smul] at commutator
      exact sub_eq_zero.mp commutator
    simpa only [Module.End.mul_apply, member.2, map_smul] using
      LinearMap.congr_fun energyCommute state

def energyB0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) : Module.End ℂ (originalEnergySector D H beta level) :=
  (B D 0).restrict (original_B0_preserves_energy_sector D H beta level)

@[simp] theorem energyB0_coe (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D) (level : ℤ)
    (state : originalEnergySector D H beta level) :
    (energyB0 D H beta level state : State D) = B D 0 state := rfl

variable (D : LatticeData)
  (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
  (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
  (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
  (xAxis yAxis : Fin D.rank) (level : ℤ)

local notation "antighost" => energyB0 D H beta level
local notation "original" => energyOriginalQ D H leftGramInverse rightGramInverse beta level
local notation "leading" => energyLeading D H leftGramInverse rightGramInverse beta nullDirection level
local notation "normalizer" => energyNormalizer D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "projector" => energyProjector D H frame inverse leftGramInverse rightGramInverse
  leftFrameInverse rightFrameInverse beta xAxis yAxis level
local notation "correctionInverse" => energyCorrectionInverse D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "homotopy" => energyTransferHomotopy D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "inclusion" => energyTransferInclusion D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
local notation "projection" => energyTransferProjection D H frame inverse
  leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level

theorem energy_B0_original_ward :
    original * antighost + antighost * original =
      (chosenH D beta + (level : ℂ) - 1) • 1 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  have ward := LinearMap.congr_fun (ward_identity D H 0) state.val
  simpa only [LinearMap.add_apply, Module.End.mul_apply, energyOriginalQ_coe,
    energyB0_coe, Submodule.coe_add, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.coe_smul, state.property.2] using ward

theorem energy_B0_leading_anticommutes : leading * antighost + antighost * leading = 0 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  simpa only [LinearMap.add_apply, Module.End.mul_apply, energyLeading_coe,
    energyB0_coe, Submodule.coe_add, LinearMap.zero_apply, Submodule.coe_zero] using
    LinearMap.congr_fun (original_delta_B_zero_anticommutes D
      (adaptedPartner D beta nullDirection) (chosenP D beta nullDirection)) state.val

variable (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
  (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
  (nonzero : chosenP D beta nullDirection ≠ 0)

include xDual yDual nonzero in
theorem energy_B0_normalizer_anticommutes :
    normalizer * antighost + antighost * normalizer = 0 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  simpa only [LinearMap.add_apply, Module.End.mul_apply, energyNormalizer_coe,
    energyB0_coe, Submodule.coe_add, LinearMap.zero_apply, Submodule.coe_zero] using
    LinearMap.congr_fun (original_S_B_zero_anticommutes D frame inverse
      leftFrameInverse rightFrameInverse xAxis yAxis xDual yDual
      (chosenP D beta nullDirection) nonzero) state.val

include xDual yDual nonzero in
theorem energy_B0_projector_commutes : antighost * projector = projector * antighost := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  simpa only [Module.End.mul_apply, energyProjector_coe, energyB0_coe] using
    LinearMap.congr_fun (original_Kdagger_P_B_zero_commute D frame inverse
      leftFrameInverse rightFrameInverse xAxis yAxis xDual yDual
      (chosenP D beta nullDirection) nonzero).2 state.val

variable (shell : chosenH D beta + (level : ℂ) - 1 = 0)

include shell xDual yDual nonzero in
theorem energy_B0_finite_inverse_commutes_on_shell :
    antighost * correctionInverse = correctionInverse * antighost := by
  have normalizerAnti := energy_B0_normalizer_anticommutes D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
    xAxis yAxis level xDual yDual nonzero
  have originalAnti : original * antighost + antighost * original = 0 := by
    rw [energy_B0_original_ward, shell, zero_smul]
  have leadingAnti := energy_B0_leading_anticommutes D H leftGramInverse rightGramInverse
    beta nullDirection level
  exact (finite_B0_factor_algebra antighost original leading normalizer projector
    (2 * level.toNat + 2) originalAnti leadingAnti normalizerAnti
    (energy_B0_projector_commutes D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level xDual yDual nonzero)).1

include shell xDual yDual nonzero in
theorem energy_B0_transfer_compatibility_on_shell :
    homotopy * antighost + antighost * homotopy = 0 ∧
      antighost * inclusion = inclusion * antighost ∧
      antighost * projection = projection * antighost := by
  have normalizerAnti := energy_B0_normalizer_anticommutes D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
    xAxis yAxis level xDual yDual nonzero
  have projectorCommute := energy_B0_projector_commutes D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
    xAxis yAxis level xDual yDual nonzero
  have originalAnti : original * antighost + antighost * original = 0 := by
    rw [energy_B0_original_ward, shell, zero_smul]
  exact (finite_B0_factor_algebra antighost original leading normalizer projector
    (2 * level.toNat + 2) originalAnti
    (energy_B0_leading_anticommutes D H leftGramInverse rightGramInverse beta nullDirection level)
    normalizerAnti projectorCommute).2
      (energy_B0_finite_inverse_commutes_on_shell D H frame inverse
        leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
        xAxis yAxis level xDual yDual nonzero shell)

#print axioms original_B0_preserves_energy_sector
#print axioms energy_B0_original_ward
#print axioms energy_B0_leading_anticommutes
#print axioms energy_B0_normalizer_anticommutes
#print axioms energy_B0_projector_commutes
#print axioms energy_B0_finite_inverse_commutes_on_shell
#print axioms energy_B0_transfer_compatibility_on_shell

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
