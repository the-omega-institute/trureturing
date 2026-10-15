import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis16

set_option autoImplicit false
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem nativeLevel_nonnegative_without_axes (D : LatticeData)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) : 0 ≤ nativeLevel D powers subset :=
  add_nonneg (Int.natCast_nonneg _) (native_polarizedLevel_nonnegative subset)

theorem nativeWord_ne_zero (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (index : NativeIndex D) : nativeWord D frame beta index ≠ 0 := by
  intro vanished
  have represented := nativeCoefficients_word D frame inverse leftFrameInverse rightFrameInverse beta index
  rw [vanished, map_zero] at represented
  have impossible := congrArg (fun coefficients : NativeIndex D →₀ ℂ => coefficients index) represented
  simpa using impossible

section NativeSectorEnergy

variable (D : LatticeData)
variable (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D)

include leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse

theorem native_negative_level_vanishing (level : ℤ) (psi : State D)
    (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi)
    (negative : level < 0) : psi = 0 := by
  by_contra nonzero
  obtain ⟨index, coefficientNonzero⟩ := native_nonzero_coefficient D frame inverse
    leftFrameInverse rightFrameInverse beta psi sector nonzero
  have atLevel := nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse beta H
    leftGramInverse rightGramInverse level psi sector energy index coefficientNonzero
  exact nativeLevel_ne_of_negative D index.1 index.2 level negative atLevel

theorem native_nonzero_level_nonnegative (level : ℤ) (psi : State D)
    (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi)
    (nonzero : psi ≠ 0) : 0 ≤ level := by
  by_contra negative
  exact nonzero (native_negative_level_vanishing D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta level psi sector energy (lt_of_not_ge negative))

theorem native_absolute_auxiliary_bounds (xAxis yAxis : Fin D.rank) (level degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (nonzero : psi ≠ 0) : -level ≤ degree ∧ degree ≤ level + 1 := by
  obtain ⟨index, coefficientNonzero⟩ := native_nonzero_coefficient D frame inverse
    leftFrameInverse rightFrameInverse beta psi sector nonzero
  have atLevel := nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse beta H
    leftGramInverse rightGramInverse level psi sector energy index coefficientNonzero
  have atDegree := nativeAux_support_degree D frame inverse leftFrameInverse rightFrameInverse beta
    xAxis yAxis degree psi sector homogeneous index coefficientNonzero
  simpa only [atLevel, atDegree] using nativeDegree_bounds D xAxis yAxis index.1 index.2

theorem native_relative_auxiliary_bounds (xAxis yAxis : Fin D.rank) (level degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (relative : B D 0 psi = 0) (nonzero : psi ≠ 0) : -level ≤ degree ∧ degree ≤ level := by
  obtain ⟨index, coefficientNonzero⟩ := native_nonzero_coefficient D frame inverse
    leftFrameInverse rightFrameInverse beta psi sector nonzero
  have atLevel := nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse beta H
    leftGramInverse rightGramInverse level psi sector energy index coefficientNonzero
  have atDegree := nativeAux_support_degree D frame inverse leftFrameInverse rightFrameInverse beta
    xAxis yAxis degree psi sector homogeneous index coefficientNonzero
  have absent := native_relative_support D frame inverse leftFrameInverse rightFrameInverse beta
    psi sector relative index coefficientNonzero
  simpa only [atLevel, atDegree] using nativeDegree_relative_bounds D xAxis yAxis index.1 index.2 absent

theorem native_absolute_fixed_energy (xAxis yAxis : Fin D.rank) (level degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (nonzero : psi ≠ 0) : 0 ≤ level ∧ -level ≤ degree ∧ degree ≤ level + 1 :=
  ⟨native_nonzero_level_nonnegative D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta level psi sector energy nonzero,
    native_absolute_auxiliary_bounds D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level degree psi sector energy homogeneous nonzero⟩

theorem native_relative_fixed_energy (xAxis yAxis : Fin D.rank) (level degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (relative : B D 0 psi = 0) (nonzero : psi ≠ 0) : 0 ≤ level ∧ -level ≤ degree ∧ degree ≤ level :=
  ⟨native_nonzero_level_nonnegative D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta level psi sector energy nonzero,
    native_relative_auxiliary_bounds D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta xAxis yAxis level degree psi sector energy homogeneous relative nonzero⟩

theorem native_absolute_level_zero (xAxis yAxis : Fin D.rank) (degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta - 1) • psi)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (nonzero : psi ≠ 0) : degree = 0 ∨ degree = 1 := by
  have normalized : (M D H 0 + G D 0) psi = (chosenH D beta + ((0 : ℤ) : ℂ) - 1) • psi := by
    simpa using energy
  have bounds := native_absolute_auxiliary_bounds D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis 0 degree psi sector normalized homogeneous nonzero
  omega

theorem native_relative_level_zero (xAxis yAxis : Fin D.rank) (degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi)
    (energy : (M D H 0 + G D 0) psi = (chosenH D beta - 1) • psi)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (relative : B D 0 psi = 0) (nonzero : psi ≠ 0) : degree = 0 := by
  have normalized : (M D H 0 + G D 0) psi = (chosenH D beta + ((0 : ℤ) : ℂ) - 1) • psi := by
    simpa using energy
  have bounds := native_relative_auxiliary_bounds D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis 0 degree psi sector normalized homogeneous relative nonzero
  omega

theorem native_T0_zero_support_matching (psi : State D)
    (sector : chargeProjection D beta psi = psi) (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (index : NativeIndex D)
    (nonzero : nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index ≠ 0) :
    chosenH D beta + (nativeLevel D index.1 index.2 : ℂ) - 1 = 0 := by
  have evaluated := nativeT0_coefficient D frame inverse leftFrameInverse rightFrameInverse beta H
    leftGramInverse rightGramInverse psi sector index
  rw [zeroEnergy, map_zero, Finsupp.zero_apply] at evaluated
  exact (mul_eq_zero.mp evaluated.symm).resolve_right nonzero

theorem native_T0_zero_nonzero_level_matching (psi : State D)
    (sector : chargeProjection D beta psi = psi) (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (nonzero : psi ≠ 0) : ∃ level : ℤ, 0 ≤ level ∧ chosenH D beta + (level : ℂ) - 1 = 0 := by
  obtain ⟨index, coefficientNonzero⟩ := native_nonzero_coefficient D frame inverse
    leftFrameInverse rightFrameInverse beta psi sector nonzero
  exact ⟨nativeLevel D index.1 index.2, nativeLevel_nonnegative_without_axes D index.1 index.2,
    native_T0_zero_support_matching D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse beta psi sector zeroEnergy index coefficientNonzero⟩

theorem native_T0_zero_vanishing_if_no_level (psi : State D)
    (sector : chargeProjection D beta psi = psi) (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (noLevel : ¬ ∃ level : ℤ, 0 ≤ level ∧ chosenH D beta + (level : ℂ) - 1 = 0) : psi = 0 := by
  by_contra nonzero
  exact noLevel (native_T0_zero_nonzero_level_matching D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta psi sector zeroEnergy nonzero)

omit leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse in
theorem native_T0_zero_homogeneous_level (level : ℤ) (psi : State D)
    (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (matching : chosenH D beta + (level : ℂ) - 1 = 0) :
    (M D H 0 + G D 0) psi = (chosenH D beta + (level : ℂ) - 1) • psi := by
  rw [matching, zero_smul]
  exact zeroEnergy

theorem native_T0_zero_absolute_auxiliary_bounds (xAxis yAxis : Fin D.rank)
    (level degree : ℤ) (psi : State D) (sector : chargeProjection D beta psi = psi)
    (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (matching : chosenH D beta + (level : ℂ) - 1 = 0)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (nonzero : psi ≠ 0) : 0 ≤ level ∧ -level ≤ degree ∧ degree ≤ level + 1 :=
  native_absolute_fixed_energy D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis level degree psi sector
    (native_T0_zero_homogeneous_level D H beta level psi zeroEnergy matching) homogeneous nonzero

theorem native_T0_zero_relative_auxiliary_bounds (xAxis yAxis : Fin D.rank)
    (level degree : ℤ) (psi : State D) (sector : chargeProjection D beta psi = psi)
    (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (matching : chosenH D beta + (level : ℂ) - 1 = 0)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (relative : B D 0 psi = 0) (nonzero : psi ≠ 0) : 0 ≤ level ∧ -level ≤ degree ∧ degree ≤ level :=
  native_relative_fixed_energy D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis level degree psi sector
    (native_T0_zero_homogeneous_level D H beta level psi zeroEnergy matching) homogeneous relative nonzero

end NativeSectorEnergy

theorem native_matching_level_unique (D : LatticeData) (beta : Charge D) (first second : ℤ)
    (firstMatching : chosenH D beta + (first : ℂ) - 1 = 0)
    (secondMatching : chosenH D beta + (second : ℂ) - 1 = 0) : first = second := by
  have integerCasts : (first : ℂ) = (second : ℂ) := by
    linear_combination firstMatching - secondMatching
  exact_mod_cast integerCasts

theorem native_absolute_window_cardinality (level : ℤ) (nonnegative : 0 ≤ level) :
    ((Finset.Icc (-level) (level + 1)).card : ℤ) = 2 * level + 2 := by
  calc
    ((Finset.Icc (-level) (level + 1)).card : ℤ) = level + 1 + 1 - (-level) :=
      Int.card_Icc_of_le (a := -level) (b := level + 1) (by omega)
    _ = 2 * level + 2 := by omega

theorem native_relative_window_cardinality (level : ℤ) (nonnegative : 0 ≤ level) :
    ((Finset.Icc (-level) level).card : ℤ) = 2 * level + 1 := by
  calc
    ((Finset.Icc (-level) level).card : ℤ) = level + 1 - (-level) :=
      Int.card_Icc_of_le (a := -level) (b := level) (by omega)
    _ = 2 * level + 1 := by omega

theorem native_down_level_zero (D : LatticeData) : nativeLevel D 0 ∅ = 0 := by
  simp [nativeLevel, Finsupp.weight_apply, polarizedLevel]

theorem native_up_level_zero (D : LatticeData) : nativeLevel D 0 {3} = 0 := by
  simp [nativeLevel, Finsupp.weight_apply, polarizedLevel, polarizedWeight,
    BcGhostLZeroSpectrum.siteWeight]

theorem native_down_degree_zero (D : LatticeData) (xAxis yAxis : Fin D.rank) :
    nativeDegree D xAxis yAxis 0 ∅ = 0 := by
  simp [nativeDegree, Finsupp.weight_apply, epsilonCount, thetaCount, etaCount]

theorem native_up_degree_one (D : LatticeData) (xAxis yAxis : Fin D.rank) :
    nativeDegree D xAxis yAxis 0 {3} = 1 := by
  norm_num [nativeDegree, Finsupp.weight_apply, epsilonCount, thetaCount, etaCount,
    Finset.filter_singleton]

theorem native_absolute_level_zero_witness (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) :
    ∃ psi : State D, chargeProjection D beta psi = psi ∧ psi ≠ 0 ∧
      (M D H 0 + G D 0) psi = (chosenH D beta - 1) • psi ∧
      AuxHomogeneous D frame inverse xAxis yAxis 1 psi ∧ B D 0 psi ≠ 0 := by
  let psi := nativeWord D frame beta (0, {3})
  have energy := nativeWord_T0 D H frame leftGramInverse rightGramInverse beta (0, {3})
  have homogeneous := nativeWord_aux D frame inverse rightFrameInverse xAxis yAxis beta (0, {3})
  have ghostAction : B D 0 psi = nativeWord D frame beta (0, ∅) := by
    simpa [psi, sign, Finset.filter_singleton] using nativeWord_Bzero D frame beta (0, {3})
  refine ⟨psi, nativeWord_sector D frame beta (0, {3}),
    nativeWord_ne_zero D frame inverse leftFrameInverse rightFrameInverse beta (0, {3}), ?_, ?_, ?_⟩
  · simpa [psi, native_up_level_zero] using energy
  · simpa [AuxHomogeneous, psi, native_up_degree_one] using homogeneous
  · rw [ghostAction]
    exact nativeWord_ne_zero D frame inverse leftFrameInverse rightFrameInverse beta (0, ∅)

theorem native_relative_level_zero_witness (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) :
    ∃ psi : State D, chargeProjection D beta psi = psi ∧ psi ≠ 0 ∧
      (M D H 0 + G D 0) psi = (chosenH D beta - 1) • psi ∧
      AuxHomogeneous D frame inverse xAxis yAxis 0 psi ∧ B D 0 psi = 0 := by
  let psi := nativeWord D frame beta (0, ∅)
  have energy := nativeWord_T0 D H frame leftGramInverse rightGramInverse beta (0, ∅)
  have homogeneous := nativeWord_aux D frame inverse rightFrameInverse xAxis yAxis beta (0, ∅)
  refine ⟨psi, nativeWord_sector D frame beta (0, ∅),
    nativeWord_ne_zero D frame inverse leftFrameInverse rightFrameInverse beta (0, ∅), ?_, ?_, ?_⟩
  · simpa [psi, native_down_level_zero] using energy
  · simpa [AuxHomogeneous, psi, native_down_degree_zero] using homogeneous
  · simpa [psi] using nativeWord_Bzero D frame beta (0, ∅)

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
