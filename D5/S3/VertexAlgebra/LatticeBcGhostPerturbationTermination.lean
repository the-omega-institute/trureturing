/- GID: D5/S3/VertexAlgebra/LatticeBcGhostPerturbationTermination
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostPerturbationTermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized original-Q perturbation terminates on each fixed energy sector. -/

import D5.S3.VertexAlgebra.LatticeBcGhostFixedEnergyFiltration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

private theorem chargeProjection_tmul (D : LatticeData) (beta : Charge D)
    (matter : Carrier D) (ghost : Fock ℂ) :
    chargeProjection D beta (matter ⊗ₜ[ℂ] ghost) = Finsupp.single beta (matter beta) ⊗ₜ[ℂ] ghost := by
  simp [chargeProjection, chargeExtraction, chargeEmbedding, TensorProduct.map_tmul,
    Finsupp.lsingle, Finsupp.lapply]

private theorem O_single (D : LatticeData) (direction : Fin D.rank → ℂ)
    (mode : ℤ) (beta : Charge D) (polynomial : Oscillator D) (ghost : Fock ℂ) :
    O D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost) =
      Finsupp.single beta (directionalPolynomialCurrent D direction beta mode polynomial) ⊗ₜ[ℂ] ghost := by
  have matter : directionalCurrent D direction mode (Finsupp.single beta polynomial) =
      Finsupp.single beta (directionalPolynomialCurrent D direction beta mode polynomial) := by
    simp [directionalCurrent, directionalPolynomialCurrent, neutralMode_single,
      Finsupp.single_finsetSum, Finsupp.smul_single]
  simpa only [O, TensorProduct.map_tmul, LinearMap.id_apply] using
    congrArg (fun value => value ⊗ₜ[ℂ] ghost) matter

private theorem dAtom_sector (D : LatticeData) (direction : Fin D.rank → ℂ)
    (mode : ℤ) (beta : Charge D) (polynomial : Oscillator D) (ghost : Fock ℂ) :
    chargeProjection D beta (dAtom D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)) =
      dAtom D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost) := by
  by_cases zeroMode : mode = 0
  · simp [dAtom, zeroMode]
  · simp [dAtom, zeroMode, Module.End.mul_apply, O_single, C,
      TensorProduct.map_tmul, chargeProjection_tmul]

private theorem rAtom_sector (D : LatticeData) (direction : Fin D.rank → ℂ)
    (mode : ℤ) (beta : Charge D) (polynomial : Oscillator D) (ghost : Fock ℂ) :
    chargeProjection D beta (rAtom D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)) =
      rAtom D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost) := by
  by_cases zeroMode : mode = 0
  · simp [rAtom, zeroMode]
  · simp [rAtom, zeroMode, Module.End.mul_apply, O_single, B,
      TensorProduct.map_tmul, chargeProjection_tmul]

private theorem sector_from_tmul (D : LatticeData) (beta : Charge D)
    (operator : Module.End ℂ (State D))
    (onTmul : ∀ polynomial ghost,
      chargeProjection D beta (operator (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)) =
        operator (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost))
    (state : State D) (sector : chargeProjection D beta state = state) :
    chargeProjection D beta (operator state) = operator state := by
  have onInput (input : Oscillator D ⊗[ℂ] Fock ℂ) :
      chargeProjection D beta (operator (chargeEmbedding D beta input)) =
        operator (chargeEmbedding D beta input) := by
    induction input using TensorProduct.induction_on with
    | zero => simp
    | tmul polynomial ghost =>
        simpa only [chargeEmbedding, TensorProduct.map_tmul, Finsupp.lsingle_apply, LinearMap.id_apply]
          using onTmul polynomial ghost
    | add first second firstProof secondProof => simp [firstProof, secondProof]
  obtain ⟨input, equality⟩ := (chargeEmbedding_range_iff D beta state).mpr sector
  rw [← equality]
  exact onInput input

private theorem dSum_sector (D : LatticeData) (direction : Fin D.rank → ℂ)
    (beta : Charge D) (state : State D) (sector : chargeProjection D beta state = state) :
    chargeProjection D beta (dSum D direction state) = dSum D direction state := by
  apply sector_from_tmul D beta (dSum D direction) _ state sector
  intro polynomial ghost
  change chargeProjection D beta (∑ᶠ mode : ℤ, dAtom D direction mode
    (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)) =
      ∑ᶠ mode : ℤ, dAtom D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)
  calc
    _ = ∑ᶠ mode : ℤ, chargeProjection D beta
        (dAtom D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)) :=
      (chargeProjection D beta).toAddMonoidHom.map_finsum (dAtom_finite D direction _)
    _ = _ := finsum_congr (fun mode => dAtom_sector D direction mode beta polynomial ghost)

private theorem R_sector (D : LatticeData) (direction : Fin D.rank → ℂ)
    (coefficient : ℂ) (beta : Charge D) (state : State D)
    (sector : chargeProjection D beta state = state) :
    chargeProjection D beta (R D direction coefficient state) = R D direction coefficient state := by
  have summed : chargeProjection D beta (rSum D direction state) = rSum D direction state := by
    apply sector_from_tmul D beta (rSum D direction) _ state sector
    intro polynomial ghost
    change chargeProjection D beta (∑ᶠ mode : ℤ, rAtom D direction mode
      (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)) =
        ∑ᶠ mode : ℤ, rAtom D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)
    calc
      _ = ∑ᶠ mode : ℤ, chargeProjection D beta
          (rAtom D direction mode (Finsupp.single beta polynomial ⊗ₜ[ℂ] ghost)) :=
        (chargeProjection D beta).toAddMonoidHom.map_finsum (rAtom_finite D direction _)
      _ = _ := finsum_congr (fun mode => rAtom_sector D direction mode beta polynomial ghost)
  simpa only [R, LinearMap.smul_apply, map_smul, summed]

private theorem Q_sector (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (state : State D) (sector : chargeProjection D beta state = state) :
    chargeProjection D beta (Q D H state) = Q D H state := by
  apply sector_from_tmul D beta (Q D H) _ state sector
  intro polynomial ghost
  rw [Q_tmul]
  simp only [map_sum, map_add, map_smul, sugawaraMode_single_sector, chargeProjection_tmul,
    Finsupp.single_eq_same]

private theorem totalZero_C_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) :
    (M D H 0 + G D 0) * C D mode - C D mode * (M D H 0 + G D 0) =
      -(mode : ℂ) • C D mode := by
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostStressCurrent.L_c_commutator (K := ℂ) 0 mode)
  simp only [map_sub, map_smul, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul,
    Int.cast_zero, mul_zero, zero_add, zero_sub] at lifted
  change G D 0 * C D mode - C D mode * G D 0 = _ at lifted
  have matter : M D H 0 * C D mode = C D mode * M D H 0 := by
    apply TensorProduct.ext'
    intro matterState ghostState
    simp [M, C, Module.End.mul_apply]
  calc
    _ = (M D H 0 * C D mode - C D mode * M D H 0) +
        (G D 0 * C D mode - C D mode * G D 0) := by noncomm_ring
    _ = _ := by rw [matter, sub_self, zero_add]; exact lifted

private theorem totalZero_dSum_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (direction : Fin D.rank → ℂ) :
    (M D H 0 + G D 0) * dSum D direction = dSum D direction * (M D H 0 + G D 0) := by
  have atom (mode : ℤ) : (M D H 0 + G D 0) * dAtom D direction mode =
      dAtom D direction mode * (M D H 0 + G D 0) := by
    by_cases zeroMode : mode = 0
    · simp [dAtom, zeroMode]
    apply sub_eq_zero.mp
    simp only [dAtom, if_neg zeroMode]
    calc
      _ = ((M D H 0 + G D 0) * C D (-mode) -
          C D (-mode) * (M D H 0 + G D 0)) * O D direction mode +
          C D (-mode) * ((M D H 0 + G D 0) * O D direction mode -
          O D direction mode * (M D H 0 + G D 0)) := by
            simp only [sub_mul, mul_sub, mul_assoc]
            abel
      _ = 0 := by
        rw [totalZero_C_commutator, totalZero_O_commutator D H leftGramInverse rightGramInverse]
        simp only [Int.cast_neg, neg_neg, smul_mul_assoc, mul_smul_comm, ← add_smul,
          add_neg_cancel, zero_smul]
  apply LinearMap.ext
  intro state
  change (M D H 0 + G D 0) (∑ᶠ mode : ℤ, dAtom D direction mode state) =
    ∑ᶠ mode : ℤ, dAtom D direction mode ((M D H 0 + G D 0) state)
  calc
    _ = ∑ᶠ mode : ℤ, (M D H 0 + G D 0) (dAtom D direction mode state) :=
      (M D H 0 + G D 0).toAddMonoidHom.map_finsum (dAtom_finite D direction state)
    _ = _ := finsum_congr (fun mode => LinearMap.congr_fun (atom mode) state)

private theorem totalZero_Q_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1) :
    (M D H 0 + G D 0) * Q D H = Q D H * (M D H 0 + G D 0) := by
  have covariance := LatticeBcGhostBrstTotalCovariance.total_covariance D H leftGramInverse rightGramInverse 0
  simp at covariance
  exact (sub_eq_zero.mp covariance).symm

section Filtration

variable (D : LatticeData)
variable (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
variable (xAxis yAxis : Fin D.rank)

local notation "normalizer" => S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis (chosenP D beta nullDirection)
local notation "leading" => delta D (adaptedPartner D beta nullDirection) (chosenP D beta nullDirection)
local notation "totalZero" => M D H 0 + G D 0

def originalPerturbation : Module.End ℂ (State D) := normalizer * (Q D H - leading)

def signedEnergyFiltration (level lower : ℤ) : Submodule ℂ (State D) :=
  Submodule.span ℂ (nativeWord D frame beta ''
    {index : NativeIndex D | nativeLevel D index.1 index.2 = level ∧
      lower ≤ nativeDegree D xAxis yAxis index.1 index.2})

private theorem normalized_sector (state : State D) (sector : chargeProjection D beta state = state) :
    chargeProjection D beta (normalizer state) = normalizer state := by
  have inverseSector : chargeProjection D beta
      (Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis state) =
      Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis state := by
    rw [← native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta state sector]
    simp only [map_sum, map_smul]
    have onWord (index : NativeIndex D) :
        Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
          (nativeWord D frame beta index) = (kappa D xAxis yAxis index.1 index.2 : ℂ)⁻¹ •
            nativeWord D frame beta index :=
      Kdagger_native D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis beta index.1 1 index.2
    simp only [onWord, map_smul, nativeWord_sector]
  exact R_sector D (frame xAxis) (chosenP D beta nullDirection) beta _ inverseSector

include leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse in
private theorem homogeneous_mem_filtration (level degree lower : ℤ)
    (state : State D) (sector : chargeProjection D beta state = state)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree state)
    (above : lower ≤ degree) :
    state ∈ signedEnergyFiltration D frame beta xAxis yAxis level lower := by
  rw [← native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta state sector]
  apply Submodule.sum_mem
  intro index present
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have nonzero := Finsupp.mem_support_iff.mp present
  have atLevel := nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse beta H
    leftGramInverse rightGramInverse level state sector energy index nonzero
  have atDegree := nativeAux_support_degree D frame inverse leftFrameInverse rightFrameInverse beta
    xAxis yAxis degree state sector homogeneous index nonzero
  exact ⟨index, ⟨atLevel, by rw [atDegree]; exact above⟩, rfl⟩

private theorem filtration_exhausted (level lower : ℤ) (above : level + 1 < lower) :
    signedEnergyFiltration D frame beta xAxis yAxis level lower = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro state ⟨index, ⟨atLevel, atDegree⟩, rfl⟩
  have upper := (nativeDegree_bounds D xAxis yAxis index.1 index.2).2
  rw [atLevel] at upper
  omega

include leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse in
private theorem energy_mem_filtration (level : ℤ) (state : State D)
    (sector : chargeProjection D beta state = state)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state) :
    state ∈ signedEnergyFiltration D frame beta xAxis yAxis level (-level) := by
  rw [← native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta state sector]
  apply Submodule.sum_mem
  intro index present
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have atLevel := nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse beta H
    leftGramInverse rightGramInverse level state sector energy index (Finsupp.mem_support_iff.mp present)
  have lower := (nativeDegree_bounds D xAxis yAxis index.1 index.2).1
  exact ⟨index, ⟨atLevel, by simpa only [atLevel] using lower⟩, rfl⟩

private theorem eigen_map (operator : Module.End ℂ (State D))
    (commutation : totalZero * operator = operator * totalZero)
    (level : ℤ) (state : State D)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state) :
    totalZero (operator state) = (chosenH D beta + (level : ℂ) - 1) • operator state := by
  have equation := LinearMap.congr_fun commutation state
  simpa only [Module.End.mul_apply, energy, map_smul] using equation

include leftGramInverse rightGramInverse in
private theorem original_perturbation_raises
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level lower : ℤ) (state : State D)
    (member : state ∈ signedEnergyFiltration D frame beta xAxis yAxis level lower) :
    originalPerturbation D H frame inverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis state ∈
      signedEnergyFiltration D frame beta xAxis yAxis level (lower + 1) := by
  have qCommutes := totalZero_Q_commutes D H leftGramInverse rightGramInverse
  have longitudinalCommutes := totalZero_dSum_commutes D H leftGramInverse rightGramInverse
    (adaptedPartner D beta nullDirection)
  have nullCommutes := totalZero_dSum_commutes D H leftGramInverse rightGramInverse nullDirection
  have oneCommutes : totalZero * raisingOne D H beta nullDirection =
      raisingOne D H beta nullDirection * totalZero := by
    simp only [raisingOne, delta, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    rw [qCommutes, longitudinalCommutes, nullCommutes]
  have twoCommutes : totalZero * raisingTwo D beta nullDirection =
      raisingTwo D beta nullDirection * totalZero := by
    simp only [raisingTwo, mul_smul_comm, smul_mul_assoc]
    rw [nullCommutes]
  have sCommutes := native_totalZero_S_commutes D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis H leftGramInverse rightGramInverse (chosenP D beta nullDirection)
  have auxCommutes := native_auxiliary_S_commutes D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual (chosenP D beta nullDirection)
  have inclusion : signedEnergyFiltration D frame beta xAxis yAxis level lower ≤
      (signedEnergyFiltration D frame beta xAxis yAxis level (lower + 1)).comap
        (originalPerturbation D H frame inverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis) := by
    apply Submodule.span_le.mpr
    rintro state ⟨index, ⟨atLevel, atDegree⟩, rfl⟩
    let word := nativeWord D frame beta index
    have wordSector : chargeProjection D beta word = word := nativeWord_sector D frame beta index
    have wordEnergy : totalZero word = (chosenH D beta + (level : ℂ) - 1) • word := by
      simpa only [atLevel] using nativeWord_T0 D H frame leftGramInverse rightGramInverse beta index
    have wordHomogeneous : AuxHomogeneous D frame inverse xAxis yAxis
        (nativeDegree D xAxis yAxis index.1 index.2) word :=
      nativeWord_aux D frame inverse rightFrameInverse xAxis yAxis beta index
    obtain ⟨split, oneHomogeneous, twoHomogeneous, _, _⟩ :=
      original_Q_strict_auxiliary_split D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse beta nullDirection null nonzero xAxis yAxis distinct
        xRow yRow xDual yDual _ word wordSector wordHomogeneous
    have oneSector : chargeProjection D beta (raisingOne D H beta nullDirection word) =
        raisingOne D H beta nullDirection word := by
      simp only [raisingOne, delta, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul,
        Q_sector D H beta word wordSector,
        dSum_sector D (adaptedPartner D beta nullDirection) beta word wordSector,
        dSum_sector D nullDirection beta word wordSector]
    have twoSector : chargeProjection D beta (raisingTwo D beta nullDirection word) =
        raisingTwo D beta nullDirection word := by
      simp only [raisingTwo, LinearMap.smul_apply, map_smul,
        dSum_sector D nullDirection beta word wordSector]
    have oneNormalizedHomogeneous : AuxHomogeneous D frame inverse xAxis yAxis
        (nativeDegree D xAxis yAxis index.1 index.2 + 1)
        (normalizer (raisingOne D H beta nullDirection word)) := by
      unfold AuxHomogeneous at oneHomogeneous ⊢
      have equation := LinearMap.congr_fun auxCommutes (raisingOne D H beta nullDirection word)
      simpa only [Module.End.mul_apply, oneHomogeneous, map_smul] using equation
    have twoNormalizedHomogeneous : AuxHomogeneous D frame inverse xAxis yAxis
        (nativeDegree D xAxis yAxis index.1 index.2 + 2)
        (normalizer (raisingTwo D beta nullDirection word)) := by
      unfold AuxHomogeneous at twoHomogeneous ⊢
      have equation := LinearMap.congr_fun auxCommutes (raisingTwo D beta nullDirection word)
      simpa only [Module.End.mul_apply, twoHomogeneous, map_smul] using equation
    have firstMember := homogeneous_mem_filtration D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level
      (nativeDegree D xAxis yAxis index.1 index.2 + 1) (lower + 1)
      (normalizer (raisingOne D H beta nullDirection word))
      (normalized_sector D frame inverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis _ oneSector)
      (eigen_map D H beta normalizer sCommutes level _
        (eigen_map D H beta _ oneCommutes level word wordEnergy))
      oneNormalizedHomogeneous (by omega)
    have secondMember := homogeneous_mem_filtration D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level
      (nativeDegree D xAxis yAxis index.1 index.2 + 2) (lower + 1)
      (normalizer (raisingTwo D beta nullDirection word))
      (normalized_sector D frame inverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis _ twoSector)
      (eigen_map D H beta normalizer sCommutes level _
        (eigen_map D H beta _ twoCommutes level word wordEnergy))
      twoNormalizedHomogeneous (by omega)
    change normalizer ((Q D H - leading) word) ∈
      signedEnergyFiltration D frame beta xAxis yAxis level (lower + 1)
    rw [split, map_add]
    exact Submodule.add_mem _ firstMember secondMember
  exact inclusion member

include leftGramInverse rightGramInverse in
theorem original_normalized_perturbation_termination
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) (state : State D) (sector : chargeProjection D beta state = state)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state) :
    ((normalizer * (Q D H - leading)) ^ (2 * level.toNat + 2)) state = 0 := by
  let perturbation := originalPerturbation D H frame inverse leftFrameInverse rightFrameInverse
    beta nullDirection xAxis yAxis
  have iterated (steps : ℕ) : (perturbation ^ steps) state ∈
      signedEnergyFiltration D frame beta xAxis yAxis level (-level + (steps : ℤ)) := by
    induction steps with
    | zero =>
        simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero] using
          energy_mem_filtration D H frame inverse leftGramInverse rightGramInverse
            leftFrameInverse rightFrameInverse beta xAxis yAxis level state sector energy
    | succ steps inductionHypothesis =>
        have raised := original_perturbation_raises D H frame inverse leftGramInverse rightGramInverse
          leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
          xRow yRow xDual yDual level (-level + (steps : ℤ)) _ inductionHypothesis
        simpa only [perturbation, pow_succ', Module.End.mul_apply, Nat.cast_add, Nat.cast_one,
          add_assoc] using raised
  have exhausted := filtration_exhausted D frame beta xAxis yAxis level
    (-level + ((2 * level.toNat + 2 : ℕ) : ℤ)) (by omega)
  have terminal := iterated (2 * level.toNat + 2)
  rw [exhausted] at terminal
  exact terminal

end Filtration

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
