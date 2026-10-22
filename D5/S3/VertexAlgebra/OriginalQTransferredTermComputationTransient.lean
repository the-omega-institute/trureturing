import D5.S3.VertexAlgebra.OriginalQFixedEnergyTransferTransient

set_option autoImplicit false

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
local notation "normalized" => S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
  (chosenP D beta nullDirection)
local notation "leading" => delta D (adaptedPartner D beta nullDirection) (chosenP D beta nullDirection)
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "correction" => normalized * (Q D H - leading)

theorem native_projector_degree (distinct : xAxis ≠ yAxis) (index : NativeIndex D)
    (zero : kappa D xAxis yAxis index.1 index.2 = 0) :
    nativeDegree D xAxis yAxis index.1 index.2 = epsilonCount index.2 := by
  have characterization := (kappa_zero_iff D xAxis yAxis index.1 index.2).mp zero
  have xZero := (axisExponentCount_zero_iff D xAxis index.1).mpr characterization.1
  have yZero := (axisExponentCount_zero_iff D yAxis index.1).mpr characterization.2.1
  have ghostZero := (ghost_occupation_zero_iff index.2).mpr characterization.2.2
  simp only [nativeDegree, signed_weight_axis_counts D xAxis yAxis distinct, xZero, yZero,
    ghostZero.1, ghostZero.2, Nat.cast_zero, sub_zero, zero_sub, zero_add, add_zero]

theorem projector_kills_upper_filtration (distinct : xAxis ≠ yAxis) (level lower : ℤ)
    (upper : 2 ≤ lower) (state : State D)
    (member : state ∈ signedEnergyFiltration D frame beta xAxis yAxis level lower) :
    projector state = 0 := by
  have inclusion : signedEnergyFiltration D frame beta xAxis yAxis level lower ≤ LinearMap.ker projector := by
    apply Submodule.span_le.mpr
    rintro state ⟨index, ⟨atLevel, atDegree⟩, rfl⟩
    change projector (nativeWord D frame beta index) = 0
    have nonzero : kappa D xAxis yAxis index.1 index.2 ≠ 0 := by
      intro zero
      have degree := native_projector_degree D xAxis yAxis distinct index zero
      unfold epsilonCount at degree
      split_ifs at degree <;> omega
    change projector (nativeState D frame beta index.1 1 index.2) = 0
    rw [P_native, if_neg nonzero, zero_smul]
  exact inclusion member

theorem projector_positive_epsilon (distinct : xAxis ≠ yAxis) (level : ℤ) (state : State D)
    (member : state ∈ signedEnergyFiltration D frame beta xAxis yAxis level 1) :
    C D 0 (B D 0 (projector state)) = projector state := by
  have inclusion : signedEnergyFiltration D frame beta xAxis yAxis level 1 ≤
      LinearMap.ker (C D 0 * B D 0 * projector - projector) := by
    apply Submodule.span_le.mpr
    rintro state ⟨index, ⟨atLevel, atDegree⟩, rfl⟩
    change C D 0 (B D 0 (projector (nativeWord D frame beta index))) -
      projector (nativeWord D frame beta index) = 0
    have onWord := P_native D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis beta index.1 1 index.2
    change projector (nativeWord D frame beta index) = _ at onWord
    by_cases zero : kappa D xAxis yAxis index.1 index.2 = 0
    · have degree := native_projector_degree D xAxis yAxis distinct index zero
      have present : 3 ∈ index.2 := by
        by_contra absent
        simp only [epsilonCount, if_neg absent] at degree
        omega
      rw [onWord, if_pos zero, one_smul]
      change C D 0 (B D 0 (nativeWord D frame beta index)) - nativeWord D frame beta index = 0
      rw [nativeWord_Czero_Bzero D frame beta index, if_pos present, sub_self]
    · rw [onWord, if_neg zero, zero_smul, map_zero, map_zero, sub_self]
  exact sub_eq_zero.mp (inclusion member)

include leftGramInverse rightGramInverse in
theorem projector_lower_filtration (distinct : xAxis ≠ yAxis) (level : ℤ) (state : State D)
    (sector : chargeProjection D beta state = state)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state) :
    projector state ∈ signedEnergyFiltration D frame beta xAxis yAxis level 0 := by
  rw [← native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta state sector]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro index present
  apply Submodule.smul_mem
  have onWord := P_native D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis beta index.1 1 index.2
  change projector (nativeWord D frame beta index) = _ at onWord
  rw [onWord]
  by_cases zero : kappa D xAxis yAxis index.1 index.2 = 0
  · rw [if_pos zero, one_smul]
    apply Submodule.subset_span
    have atLevel := nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse beta H
      leftGramInverse rightGramInverse level state sector energy index (Finsupp.mem_support_iff.mp present)
    have degree := native_projector_degree D xAxis yAxis distinct index zero
    have nonnegative : 0 ≤ nativeDegree D xAxis yAxis index.1 index.2 := by
      rw [degree]
      unfold epsilonCount
      split_ifs <;> omega
    exact ⟨index, ⟨atLevel, nonnegative⟩, rfl⟩
  · rw [if_neg zero, zero_smul]
    exact Submodule.zero_mem _

include leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse in
theorem original_correction_raises_filtration
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level lower : ℤ) (state : State D)
    (member : state ∈ signedEnergyFiltration D frame beta xAxis yAxis level lower) :
    (Q D H - leading) state ∈ signedEnergyFiltration D frame beta xAxis yAxis level (lower + 1) := by
  have qCommutes := (terminationSupplier "totalZero_Q_commutes") D H leftGramInverse rightGramInverse
  have longitudinalCommutes := (terminationSupplier "totalZero_dSum_commutes") D H
    leftGramInverse rightGramInverse (adaptedPartner D beta nullDirection)
  have nullCommutes := (terminationSupplier "totalZero_dSum_commutes") D H
    leftGramInverse rightGramInverse nullDirection
  have oneCommutes : totalZero * raisingOne D H beta nullDirection =
      raisingOne D H beta nullDirection * totalZero := by
    simp only [raisingOne, delta, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    rw [qCommutes, longitudinalCommutes, nullCommutes]
  have twoCommutes : totalZero * raisingTwo D beta nullDirection =
      raisingTwo D beta nullDirection * totalZero := by
    simp only [raisingTwo, mul_smul_comm, smul_mul_assoc]
    rw [nullCommutes]
  have inclusion : signedEnergyFiltration D frame beta xAxis yAxis level lower ≤
      (signedEnergyFiltration D frame beta xAxis yAxis level (lower + 1)).comap (Q D H - leading) := by
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
        (terminationSupplier "Q_sector") D H beta word wordSector,
        (terminationSupplier "dSum_sector") D (adaptedPartner D beta nullDirection) beta word wordSector,
        (terminationSupplier "dSum_sector") D nullDirection beta word wordSector]
    have twoSector : chargeProjection D beta (raisingTwo D beta nullDirection word) =
        raisingTwo D beta nullDirection word := by
      simp only [raisingTwo, LinearMap.smul_apply, map_smul,
        (terminationSupplier "dSum_sector") D nullDirection beta word wordSector]
    have firstMember := (terminationSupplier "homogeneous_mem_filtration") D H frame inverse
      leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level
      (nativeDegree D xAxis yAxis index.1 index.2 + 1) (lower + 1)
      (raisingOne D H beta nullDirection word) oneSector
      ((terminationSupplier "eigen_map") D H beta _ oneCommutes level word wordEnergy)
      oneHomogeneous (by omega)
    have secondMember := (terminationSupplier "homogeneous_mem_filtration") D H frame inverse
      leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta xAxis yAxis level
      (nativeDegree D xAxis yAxis index.1 index.2 + 2) (lower + 1)
      (raisingTwo D beta nullDirection word) twoSector
      ((terminationSupplier "eigen_map") D H beta _ twoCommutes level word wordEnergy)
      twoHomogeneous (by omega)
    change (Q D H - leading) word ∈
      signedEnergyFiltration D frame beta xAxis yAxis level (lower + 1)
    rw [split]
    exact Submodule.add_mem _ firstMember secondMember
  exact inclusion member

include leftGramInverse rightGramInverse in
theorem original_transferred_tail_vanishes
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D beta nullDirection ≠ 0)
    (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D beta nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (level : ℤ) (state : State D) (sector : chargeProjection D beta state = state)
    (energy : totalZero state = (chosenH D beta + (level : ℂ) - 1) • state) :
    finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
      beta nullDirection xAxis yAxis level state = projector ((Q D H - leading) (projector state)) := by
  have iterated (steps : ℕ) : ((-correction) ^ steps) (projector state) ∈
      signedEnergyFiltration D frame beta xAxis yAxis level (steps : ℤ) := by
    induction steps with
    | zero =>
      simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero] using
        projector_lower_filtration D H frame inverse leftGramInverse rightGramInverse
          leftFrameInverse rightFrameInverse beta xAxis yAxis distinct level state sector energy
    | succ steps inductionHypothesis =>
      have raised := (terminationSupplier "original_perturbation_raises") D H frame inverse
        leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection
        xAxis yAxis null nonzero distinct xRow yRow xDual yDual level (steps : ℤ) _ inductionHypothesis
      have negated := (signedEnergyFiltration D frame beta xAxis yAxis level ((steps : ℤ) + 1)).neg_mem raised
      simpa only [pow_succ', Module.End.mul_apply, LinearMap.neg_apply,
        originalPerturbation, Nat.cast_add, Nat.cast_one] using negated
  simp only [finiteOriginalTransferredDifferential, finiteOriginalCorrectionInverse,
    Module.End.mul_apply, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, Module.End.one_apply]
  · intro steps present nonzeroStep
    have raised := original_correction_raises_filtration D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
      xRow yRow xDual yDual level (steps : ℤ) _ (iterated steps)
    exact projector_kills_upper_filtration D frame inverse leftFrameInverse rightFrameInverse beta
      xAxis yAxis distinct level ((steps : ℤ) + 1) (by omega) _ raised
  · intro absent
    have present : 0 ∈ Finset.range (2 * level.toNat + 2) := Finset.mem_range.mpr (by omega)
    exact False.elim (absent present)

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
