import D5.S3.VertexAlgebra.OriginalQTransferredTermComputationTransient

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQFiniteHplCheck

theorem projected_ward_ring {Algebra : Type*} [Ring Algebra]
    (projector original antighost energy : Algebra)
    (projectorSquare : projector * projector = projector)
    (antighostProjector : antighost * projector = projector * antighost)
    (energyProjector : energy * projector = projector * energy)
    (ward : original * antighost + antighost * original = energy) :
    (projector * original * projector) * antighost +
      antighost * (projector * original * projector) = energy * projector := by
  calc
    _ = projector * original * (projector * antighost) +
        (antighost * projector) * original * projector := by noncomm_ring
    _ = projector * original * (antighost * projector) +
        (projector * antighost) * original * projector := by
          exact congrArg₂ (fun first second => first + second)
            (congrArg (fun value => projector * original * value) antighostProjector.symm)
            (congrArg (fun value => value * original * projector) antighostProjector)
    _ = projector * (original * antighost + antighost * original) * projector := by noncomm_ring
    _ = projector * energy * projector := by rw [ward]
    _ = energy * (projector * projector) := by rw [← energyProjector, mul_assoc]
    _ = energy * projector := by rw [projectorSquare]

end D5.S3.VertexAlgebra.OriginalQFiniteHplCheck

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData)
variable (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank)

local notation "totalZero" => M D H 0 + G D 0
local notation "leading" => delta D (adaptedPartner D beta nullDirection) (chosenP D beta nullDirection)
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "projectedQ" => projector * Q D H * projector

theorem original_C_zero_square : C D 0 * C D 0 = 0 := by
  apply LinearMap.ext
  intro state
  have twice := LinearMap.congr_fun (C_C_anticommute D 0 0) state
  have scalarZero : (2 : ℂ) • ((C D 0 * C D 0) state) = 0 := by
    simpa only [LinearMap.add_apply, LinearMap.zero_apply, two_smul] using twice
  exact (smul_eq_zero.mp scalarZero).resolve_left (by norm_num)

include leftGramInverse rightGramInverse in
theorem original_projected_Q_epsilon
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) (state : State D) (sector : chargeProjection D beta state = state)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state) :
    C D 0 (B D 0 (projectedQ state)) = projectedQ state ∧ C D 0 (projectedQ state) = 0 := by
  have projectedMember := projector_lower_filtration D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis distinct level state sector energy
  have raised := original_correction_raises_filtration D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
    xRow yRow xDual yDual level 0 _ projectedMember
  have epsilon := projector_positive_epsilon D frame inverse leftFrameInverse rightFrameInverse beta
    xAxis yAxis distinct level _ raised
  have strong := original_chosen_normalized_strong_contraction D beta nullDirection
    frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct xRow yRow xDual yDual nonzero
  have deltaZero : leading (projector state) = 0 := by
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun strong.2.2.2.2.1 state
  have equalProjected : projector ((Q D H - leading) (projector state)) = projectedQ state := by
    simp only [LinearMap.sub_apply, deltaZero, sub_zero, Module.End.mul_apply]
  rw [equalProjected] at epsilon
  refine ⟨epsilon, ?_⟩
  calc
    _ = C D 0 (C D 0 (B D 0 (projectedQ state))) := congrArg (C D 0) epsilon.symm
    _ = 0 := by
      simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun (original_C_zero_square D) (B D 0 (projectedQ state))

include leftGramInverse rightGramInverse in
theorem original_projected_Q_mass_shell
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) (state : State D) (sector : chargeProjection D beta state = state)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state) :
    projectedQ state = (chosenH D beta + (level : ℂ) - 1) • C D 0 (projector state) := by
  have bSector : chargeProjection D beta (B D 0 state) = B D 0 state := by
    apply (terminationSupplier "sector_from_tmul") D beta (B D 0) _ state sector
    intro polynomial ghost
    simp only [B, LinearMap.lTensor_def, TensorProduct.map_tmul, LinearMap.id_apply,
      (terminationSupplier "chargeProjection_tmul"), Finsupp.single_eq_same]
  have bCommutes : totalZero * B D 0 = B D 0 * totalZero := by
    have commutator := totalZero_B_commutator D H 0
    simp only [Int.cast_zero, neg_zero, zero_smul] at commutator
    exact sub_eq_zero.mp commutator
  have bEnergy : totalZero (B D 0 state) = (chosenH D beta + (level : ℂ) - 1) • B D 0 state := by
    simpa only [Module.End.mul_apply, energy, map_smul] using LinearMap.congr_fun bCommutes state
  have epsilon := original_projected_Q_epsilon D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
    xRow yRow xDual yDual level state sector energy
  have epsilonB := original_projected_Q_epsilon D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
    xRow yRow xDual yDual level _ bSector bEnergy
  have bProjector := (original_Kdagger_P_B_zero_commute D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis xDual yDual (chosenP D beta nullDirection) nonzero).2
  have timeProjectorCommutes := (native_totalZero_Kdagger_P_commute D frame inverse
    leftFrameInverse rightFrameInverse xAxis yAxis H leftGramInverse rightGramInverse).2
  have ward := OriginalQFiniteHplCheck.projected_ward_ring projector (Q D H) (B D 0) totalZero
    (native_P_idempotent D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis)
    bProjector timeProjectorCommutes (ward_identity D H 0)
  let energyState : originalEnergySector D H beta level := ⟨state, sector, energy⟩
  have projectedEnergy : totalZero (projector state) =
      (chosenH D beta + (level : ℂ) - 1) • projector state := by
    simpa only [energyProjector_coe] using
      (energyProjector D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta xAxis yAxis level energyState).property.2
  have equality := congrArg (C D 0) (LinearMap.congr_fun ward state)
  change C D 0 (projectedQ (B D 0 state) + B D 0 (projectedQ state)) =
    C D 0 (totalZero (projector state)) at equality
  rw [map_add, epsilonB.2, epsilon.1, zero_add, projectedEnergy, map_smul] at equality
  exact equality

include leftGramInverse rightGramInverse in
theorem original_transferred_differential_mass_shell
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) (state : State D) (sector : chargeProjection D beta state = state)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state) :
    finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
      beta nullDirection xAxis yAxis level state =
      (chosenH D beta + (level : ℂ) - 1) • C D 0 (projector state) := by
  have strong := original_chosen_normalized_strong_contraction D beta nullDirection
    frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct xRow yRow xDual yDual nonzero
  have deltaZero : leading (projector state) = 0 := by
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun strong.2.2.2.2.1 state
  calc
    _ = projector ((Q D H - leading) (projector state)) :=
      original_transferred_tail_vanishes D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
        xRow yRow xDual yDual level state sector energy
    _ = projectedQ state := by
      simp only [LinearMap.sub_apply, deltaZero, sub_zero, Module.End.mul_apply]
    _ = _ := original_projected_Q_mass_shell D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
      xRow yRow xDual yDual level state sector energy

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
