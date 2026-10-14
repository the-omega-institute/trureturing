import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis17

set_option autoImplicit false
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem chosenH_native_integer_energy (D : LatticeData) (beta : Charge D) :
    chosenH D beta = (LatticePositiveEnergy.chargeEnergy D beta : ℂ) := by
  exact (chosenH_native_norm D beta).trans (LatticePositiveEnergy.chargeEnergy_complex_half D beta).symm

theorem native_matching_iff_integer (D : LatticeData) (beta : Charge D) (level : ℤ) :
    chosenH D beta + (level : ℂ) - 1 = 0 ↔
      LatticePositiveEnergy.chargeEnergy D beta + level - 1 = 0 := by
  rw [chosenH_native_integer_energy]
  constructor <;> intro matching <;> exact_mod_cast matching

theorem native_matching_canonical_level (D : LatticeData) (beta : Charge D) :
    chosenH D beta + ((1 - LatticePositiveEnergy.chargeEnergy D beta : ℤ) : ℂ) - 1 = 0 := by
  apply (native_matching_iff_integer D beta _).mpr
  ring

section NativeIntegerLevel

variable (D : LatticeData)
variable (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
variable (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
variable (beta : Charge D)

include leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse

theorem native_T0_zero_integer_level_nonnegative (psi : State D)
    (sector : chargeProjection D beta psi = psi) (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (nonzero : psi ≠ 0) : 0 ≤ 1 - LatticePositiveEnergy.chargeEnergy D beta := by
  obtain ⟨level, nonnegative, matching⟩ := native_T0_zero_nonzero_level_matching D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse beta psi sector zeroEnergy nonzero
  have integralMatching := (native_matching_iff_integer D beta level).mp matching
  omega

theorem native_T0_zero_integer_support (psi : State D)
    (sector : chargeProjection D beta psi = psi) (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (index : NativeIndex D)
    (nonzero : nativeCoefficients D frame inverse leftFrameInverse rightFrameInverse beta psi index ≠ 0) :
    nativeLevel D index.1 index.2 = 1 - LatticePositiveEnergy.chargeEnergy D beta := by
  have matching := native_T0_zero_support_matching D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta psi sector zeroEnergy index nonzero
  have integralMatching := (native_matching_iff_integer D beta _).mp matching
  omega

theorem native_T0_zero_vanishing_if_charge_energy_gt_one (psi : State D)
    (sector : chargeProjection D beta psi = psi) (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (tooHigh : 1 < LatticePositiveEnergy.chargeEnergy D beta) : psi = 0 := by
  by_contra nonzero
  have nonnegative := native_T0_zero_integer_level_nonnegative D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta psi sector zeroEnergy nonzero
  omega

theorem native_T0_zero_integer_absolute_bounds (xAxis yAxis : Fin D.rank) (degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi)
    (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (nonzero : psi ≠ 0) :
    0 ≤ 1 - LatticePositiveEnergy.chargeEnergy D beta ∧
      -(1 - LatticePositiveEnergy.chargeEnergy D beta) ≤ degree ∧
      degree ≤ (1 - LatticePositiveEnergy.chargeEnergy D beta) + 1 :=
  native_T0_zero_absolute_auxiliary_bounds D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis (1 - LatticePositiveEnergy.chargeEnergy D beta) degree
    psi sector zeroEnergy (native_matching_canonical_level D beta) homogeneous nonzero

theorem native_T0_zero_integer_relative_bounds (xAxis yAxis : Fin D.rank) (degree : ℤ)
    (psi : State D) (sector : chargeProjection D beta psi = psi)
    (zeroEnergy : (M D H 0 + G D 0) psi = 0)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree psi)
    (relative : B D 0 psi = 0) (nonzero : psi ≠ 0) :
    0 ≤ 1 - LatticePositiveEnergy.chargeEnergy D beta ∧
      -(1 - LatticePositiveEnergy.chargeEnergy D beta) ≤ degree ∧
      degree ≤ 1 - LatticePositiveEnergy.chargeEnergy D beta :=
  native_T0_zero_relative_auxiliary_bounds D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta xAxis yAxis (1 - LatticePositiveEnergy.chargeEnergy D beta) degree
    psi sector zeroEnergy (native_matching_canonical_level D beta) homogeneous relative nonzero

end NativeIntegerLevel

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
