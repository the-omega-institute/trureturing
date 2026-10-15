import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction17
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false

open scoped Classical

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem totalZero_O_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (direction : Fin D.rank → ℂ) (mode : ℤ) :
    (M D H 0 + G D 0) * O D direction mode - O D direction mode * (M D H 0 + G D 0) =
      -(mode : ℂ) • O D direction mode := by
  classical
  have matter : sugawaraMode D H 0 * directionalCurrent D direction mode -
      directionalCurrent D direction mode * sugawaraMode D H 0 =
      -(mode : ℂ) • directionalCurrent D direction mode := by
    calc
      _ = ∑ index, direction index • (sugawaraMode D H 0 * neutralMode D index mode -
          neutralMode D index mode * sugawaraMode D H 0) := by
        simp only [directionalCurrent, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
          smul_mul_assoc, smul_sub, Finset.sum_sub_distrib]
      _ = _ := by
        simp_rw [sugawaraMode_current_commutator D H leftGramInverse rightGramInverse,
          zero_add]
        simp only [directionalCurrent, Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro index member
        rw [mul_comm]
  have lifted := congrArg (LinearMap.rTensorHom (Fock ℂ)) matter
  simp only [map_sub, map_smul, LinearMap.coe_rTensorHom, LinearMap.rTensor_mul] at lifted
  have ghost : G D 0 * O D direction mode = O D direction mode * G D 0 := by
    apply TensorProduct.ext'
    intro matterState ghostState
    simp [G, O, Module.End.mul_apply]
  change M D H 0 * O D direction mode - O D direction mode * M D H 0 = _ at lifted
  calc
    _ = (M D H 0 * O D direction mode - O D direction mode * M D H 0) +
        (G D 0 * O D direction mode - O D direction mode * G D 0) := by noncomm_ring
    _ = _ := by
      rw [ghost, sub_self, add_zero]
      simpa only [O, LinearMap.rTensor_def] using lifted

theorem totalZero_B_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) :
    (M D H 0 + G D 0) * B D mode - B D mode * (M D H 0 + G D 0) =
      -(mode : ℂ) • B D mode := by
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostStressCurrent.L_b_commutator (K := ℂ) 0 mode)
  simp only [map_sub, map_smul, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul,
    zero_add, zero_sub] at lifted
  change G D 0 * B D mode - B D mode * G D 0 = _ at lifted
  have matter : M D H 0 * B D mode = B D mode * M D H 0 := by
    apply TensorProduct.ext'
    intro matterState ghostState
    simp [M, B, Module.End.mul_apply]
  calc
    _ = (M D H 0 * B D mode - B D mode * M D H 0) +
        (G D 0 * B D mode - B D mode * G D 0) := by noncomm_ring
    _ = _ := by
      rw [matter, sub_self, zero_add]
      simpa only [B, LinearMap.lTensor_def, Int.cast_zero, zero_sub] using lifted

theorem totalZero_rAtom_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (direction : Fin D.rank → ℂ) (mode : ℤ) :
    (M D H 0 + G D 0) * rAtom D direction mode = rAtom D direction mode * (M D H 0 + G D 0) := by
  by_cases zeroMode : mode = 0
  · simp [rAtom, zeroMode]
  have product :
      (M D H 0 + G D 0) * (O D direction (-mode) * B D mode) -
        (O D direction (-mode) * B D mode) * (M D H 0 + G D 0) = 0 := by
    calc
      _ = ((M D H 0 + G D 0) * O D direction (-mode) -
          O D direction (-mode) * (M D H 0 + G D 0)) * B D mode +
          O D direction (-mode) * ((M D H 0 + G D 0) * B D mode -
          B D mode * (M D H 0 + G D 0)) := by
        simp only [sub_mul, mul_sub, mul_assoc]
        abel
      _ = 0 := by
        rw [totalZero_O_commutator D H leftGramInverse rightGramInverse,
          totalZero_B_commutator]
        simp only [Int.cast_neg, neg_neg, smul_mul_assoc, mul_smul_comm, ← add_smul,
          add_neg_cancel, zero_smul]
  apply sub_eq_zero.mp
  have scaled := congrArg (fun operator : Module.End ℂ (State D) =>
    ((mode.natAbs : ℂ)⁻¹) • operator) product
  simpa only [rAtom, if_neg zeroMode, smul_mul_assoc, mul_smul_comm, smul_sub,
    smul_zero] using scaled

theorem totalZero_R_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (direction : Fin D.rank → ℂ) (coefficient : ℂ) :
    (M D H 0 + G D 0) * R D direction coefficient =
      R D direction coefficient * (M D H 0 + G D 0) := by
  have summed : (M D H 0 + G D 0) * rSum D direction =
      rSum D direction * (M D H 0 + G D 0) := by
    apply LinearMap.ext
    intro state
    have mapped := (M D H 0 + G D 0).toAddMonoidHom.map_finsum (rAtom_finite D direction state)
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change (M D H 0 + G D 0) (∑ᶠ mode : ℤ, rAtom D direction mode state) =
      ∑ᶠ mode : ℤ, rAtom D direction mode ((M D H 0 + G D 0) state)
    rw [mapped]
    apply finsum_congr
    intro mode
    exact congrArg (fun operator : Module.End ℂ (State D) => operator state)
      (totalZero_rAtom_commutes D H leftGramInverse rightGramInverse direction mode)
  simp only [R, mul_smul_comm, smul_mul_assoc, summed]

section NativeGrading

variable (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
  (xAxis yAxis : Fin D.rank)

local notation "nativeBasis" => nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse
local notation "inverseK" => Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "nativeAux" => auxiliary D frame inverse xAxis yAxis

theorem native_coefficient_basis_auxiliary_eigen (index : NativeCoefficientIndex D) :
    nativeAux (nativeBasis index) =
      ((Finsupp.weight (auxiliaryWeight D xAxis yAxis) index.1.2 + epsilonCount (toggleOne index.2) +
        (thetaCount (toggleOne index.2) : ℤ) - (etaCount (toggleOne index.2) : ℤ) : ℤ) : ℂ) •
        nativeBasis index := by
  rw [nativeCoefficientBasis_as_signed, map_smul]
  have native := original_coordinate_polarized_aux_degree D frame inverse rightFrameInverse
    xAxis yAxis index.1.1 index.1.2 1 (toggleOne index.2)
  change nativeAux (nativeState D frame index.1.1 index.1.2 1 (toggleOne index.2)) = _ at native
  rw [native, smul_comm]
  rfl

theorem native_auxiliary_Kdagger_P_commute :
    nativeAux * inverseK = inverseK * nativeAux ∧ nativeAux * projector = projector * nativeAux := by
  constructor
  · apply (nativeBasis).ext
    intro index
    simp only [Module.End.mul_apply, Kdagger_basis, map_smul,
      native_coefficient_basis_auxiliary_eigen D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis]
    rw [smul_comm]
  · apply (nativeBasis).ext
    intro index
    simp only [Module.End.mul_apply, P_basis, map_smul,
      native_coefficient_basis_auxiliary_eigen D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis]
    rw [smul_comm]

theorem native_auxiliary_S_commutes (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (coefficient : ℂ) :
    nativeAux * S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis coefficient =
      S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis coefficient * nativeAux := by
  have rCommutes := sub_eq_zero.mp (auxiliary_R_zero D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual coefficient)
  have inverseCommutes := (native_auxiliary_Kdagger_P_commute D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis).1
  change nativeAux * (R D (frame xAxis) coefficient * inverseK) =
    (R D (frame xAxis) coefficient * inverseK) * nativeAux
  rw [← mul_assoc, rCommutes, mul_assoc, inverseCommutes, ← mul_assoc]

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)

include leftGramInverse rightGramInverse in
theorem native_coefficient_basis_totalZero_eigen (index : NativeCoefficientIndex D) :
    (M D H 0 + G D 0) (nativeBasis index) =
      (chosenH D index.1.1 + (Finsupp.weight (frequencyWeight D) index.1.2 : ℂ) +
        (polarizedLevel (toggleOne index.2) : ℂ) - 1) • nativeBasis index := by
  rw [nativeCoefficientBasis_as_signed, map_smul]
  have native := original_total_energy_coordinate_polarized D H frame leftGramInverse rightGramInverse
    index.1.1 index.1.2 1 (toggleOne index.2)
  change (M D H 0 + G D 0)
    (nativeState D frame index.1.1 index.1.2 1 (toggleOne index.2)) = _ at native
  rw [native, smul_comm]
  rfl

include leftGramInverse rightGramInverse in
theorem native_totalZero_Kdagger_P_commute :
    (M D H 0 + G D 0) * inverseK = inverseK * (M D H 0 + G D 0) ∧
      (M D H 0 + G D 0) * projector = projector * (M D H 0 + G D 0) := by
  constructor
  · apply (nativeBasis).ext
    intro index
    simp only [Module.End.mul_apply, Kdagger_basis, map_smul,
      native_coefficient_basis_totalZero_eigen D frame inverse leftFrameInverse rightFrameInverse
        H leftGramInverse rightGramInverse]
    rw [smul_comm]
  · apply (nativeBasis).ext
    intro index
    simp only [Module.End.mul_apply, P_basis, map_smul,
      native_coefficient_basis_totalZero_eigen D frame inverse leftFrameInverse rightFrameInverse
        H leftGramInverse rightGramInverse]
    rw [smul_comm]

include leftGramInverse rightGramInverse in
theorem native_totalZero_S_commutes (coefficient : ℂ) :
    (M D H 0 + G D 0) * S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis coefficient =
      S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis coefficient * (M D H 0 + G D 0) := by
  have rCommutes := totalZero_R_commutes D H leftGramInverse rightGramInverse (frame xAxis) coefficient
  have inverseCommutes := (native_totalZero_Kdagger_P_commute D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis H leftGramInverse rightGramInverse).1
  change (M D H 0 + G D 0) * (R D (frame xAxis) coefficient * inverseK) =
    (R D (frame xAxis) coefficient * inverseK) * (M D H 0 + G D 0)
  rw [← mul_assoc, rCommutes, mul_assoc, inverseCommutes, ← mul_assoc]

end NativeGrading

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
