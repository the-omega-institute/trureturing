import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction16
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

def S (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (coefficient : ℂ) : Module.End ℂ (State D) :=
  R D (frame xAxis) coefficient *
    Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis

theorem dAtom_B_zero_anticommutes (D : LatticeData)
    (longitudinal : Fin D.rank → ℂ) (mode : ℤ) :
    dAtom D longitudinal mode * B D 0 + B D 0 * dAtom D longitudinal mode = 0 := by
  by_cases zeroMode : mode = 0
  · simp [dAtom, zeroMode]
  have ghost : C D (-mode) * B D 0 + B D 0 * C D (-mode) = 0 := by
    simpa [zeroMode] using C_B_anticommute D (-mode) 0
  simp only [dAtom, if_neg zeroMode]
  calc
    _ = C D (-mode) * (O D longitudinal mode * B D 0) +
        (B D 0 * C D (-mode)) * O D longitudinal mode := by noncomm_ring
    _ = C D (-mode) * (B D 0 * O D longitudinal mode) +
        (B D 0 * C D (-mode)) * O D longitudinal mode := by rw [O_B_commute]
    _ = (C D (-mode) * B D 0 + B D 0 * C D (-mode)) * O D longitudinal mode := by noncomm_ring
    _ = 0 := by rw [ghost, zero_mul]

theorem rAtom_B_zero_anticommutes (D : LatticeData)
    (nullDirection : Fin D.rank → ℂ) (mode : ℤ) :
    rAtom D nullDirection mode * B D 0 + B D 0 * rAtom D nullDirection mode = 0 := by
  by_cases zeroMode : mode = 0
  · simp [rAtom, zeroMode]
  have ghost := B_B_anticommute D mode 0
  have product :
      (O D nullDirection (-mode) * B D mode) * B D 0 +
        B D 0 * (O D nullDirection (-mode) * B D mode) = 0 := by
    calc
      _ = O D nullDirection (-mode) * (B D mode * B D 0) +
          (B D 0 * O D nullDirection (-mode)) * B D mode := by noncomm_ring
      _ = O D nullDirection (-mode) * (B D mode * B D 0) +
          (O D nullDirection (-mode) * B D 0) * B D mode := by rw [← O_B_commute]
      _ = O D nullDirection (-mode) * (B D mode * B D 0 + B D 0 * B D mode) := by noncomm_ring
      _ = 0 := by rw [ghost, mul_zero]
  simp only [rAtom, if_neg zeroMode, smul_mul_assoc, mul_smul_comm, ← smul_add, product, smul_zero]

theorem original_delta_B_zero_anticommutes (D : LatticeData)
    (longitudinal : Fin D.rank → ℂ) (coefficient : ℂ) :
    delta D longitudinal coefficient * B D 0 + B D 0 * delta D longitudinal coefficient = 0 := by
  have summed : dSum D longitudinal * B D 0 + B D 0 * dSum D longitudinal = 0 := by
    apply LinearMap.ext
    intro state
    have inputFinite := dAtom_finite D longitudinal state
    have outputFinite := dAtom_finite D longitudinal (B D 0 state)
    have imageFinite := inputFinite.fun_comp (map_zero (B D 0))
    have mapped := (B D 0).toAddMonoidHom.map_finsum inputFinite
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change (∑ᶠ mode : ℤ, dAtom D longitudinal mode (B D 0 state)) +
      B D 0 (∑ᶠ mode : ℤ, dAtom D longitudinal mode state) = 0
    rw [mapped, ← finsum_add_distrib outputFinite imageFinite]
    calc
      _ = ∑ᶠ mode : ℤ, (0 : State D) := by
        apply finsum_congr
        intro mode
        have identity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
          (dAtom_B_zero_anticommutes D longitudinal mode)
        simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] using identity
      _ = 0 := finsum_zero
  simp only [delta, smul_mul_assoc, mul_smul_comm, ← smul_add, summed, smul_zero]

theorem original_R_B_zero_anticommutes (D : LatticeData)
    (nullDirection : Fin D.rank → ℂ) (coefficient : ℂ) :
    R D nullDirection coefficient * B D 0 + B D 0 * R D nullDirection coefficient = 0 := by
  have summed : rSum D nullDirection * B D 0 + B D 0 * rSum D nullDirection = 0 := by
    apply LinearMap.ext
    intro state
    have inputFinite := rAtom_finite D nullDirection state
    have outputFinite := rAtom_finite D nullDirection (B D 0 state)
    have imageFinite := inputFinite.fun_comp (map_zero (B D 0))
    have mapped := (B D 0).toAddMonoidHom.map_finsum inputFinite
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change (∑ᶠ mode : ℤ, rAtom D nullDirection mode (B D 0 state)) +
      B D 0 (∑ᶠ mode : ℤ, rAtom D nullDirection mode state) = 0
    rw [mapped, ← finsum_add_distrib outputFinite imageFinite]
    calc
      _ = ∑ᶠ mode : ℤ, (0 : State D) := by
        apply finsum_congr
        intro mode
        have identity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
          (rAtom_B_zero_anticommutes D nullDirection mode)
        simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] using identity
      _ = 0 := finsum_zero
  simp only [R, smul_mul_assoc, mul_smul_comm, ← smul_add, summed, smul_zero]


section Contraction

variable (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
  (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
  (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
  (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
  (coefficient : ℂ) (nonzero : coefficient ≠ 0)

local notation "nativeBasis" => nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse
local notation "originalK" => K D (frame xAxis) (frame yAxis) (Eq.trans (xDual xAxis) (if_pos (Eq.refl xAxis)))
local notation "inverseK" => Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "projector" => P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
local notation "leading" => delta D (frame yAxis) coefficient
local notation "nullHomotopy" => R D (frame xAxis) coefficient
local notation "normalized" => S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis coefficient

include distinct yDual nonzero in
theorem original_delta_R_square_and_K_commute :
    leading * leading = 0 ∧ nullHomotopy * nullHomotopy = 0 ∧
      originalK * leading = leading * originalK ∧
      originalK * nullHomotopy = nullHomotopy * originalK := by
  have nullY : gramPair D (frame yAxis) (frame yAxis) = 0 := by
    simpa [Ne.symm distinct] using xDual yAxis
  have nullX : gramPair D (frame xAxis) (frame xAxis) = 0 := by
    simpa [distinct] using yDual xAxis
  have deltaSquare : leading * leading = 0 := by
    simp only [delta, smul_mul_assoc, mul_smul_comm, smul_smul,
      dSum_square D (frame yAxis) nullY, smul_zero]
  have rSquare : nullHomotopy * nullHomotopy = 0 := by
    simp only [R, smul_mul_assoc, mul_smul_comm, smul_smul,
      rSum_square D (frame xAxis) nullX, smul_zero]
  have anticommutator := delta_R_anticommutator D (frame xAxis) (frame yAxis)
    (by simpa using xDual xAxis) coefficient nonzero
  refine ⟨deltaSquare, rSquare, ?_, ?_⟩
  · apply sub_eq_zero.mp
    calc
      _ = nullHomotopy * (leading * leading) - (leading * leading) * nullHomotopy := by
        rw [← anticommutator]
        noncomm_ring
      _ = 0 := by rw [deltaSquare]; simp
  · apply sub_eq_zero.mp
    calc
      _ = leading * (nullHomotopy * nullHomotopy) - (nullHomotopy * nullHomotopy) * leading := by
        rw [← anticommutator]
        noncomm_ring
      _ = 0 := by rw [rSquare]; simp

include distinct xDual yDual nonzero in
theorem original_delta_R_Kdagger_P_commutations :
    (leading * inverseK = inverseK * leading ∧ leading * projector = projector * leading) ∧
      (nullHomotopy * inverseK = inverseK * nullHomotopy ∧
        nullHomotopy * projector = projector * nullHomotopy) := by
  have laws := original_delta_R_square_and_K_commute D frame xAxis yAxis distinct xDual yDual coefficient nonzero
  exact ⟨native_commutations_of_K_commutation D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis xDual yDual leading laws.2.2.1,
    native_commutations_of_K_commutation D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis xDual yDual nullHomotopy laws.2.2.2⟩

include xDual yDual in
theorem original_delta_R_P_zero : leading * projector = 0 ∧ nullHomotopy * projector = 0 := by
  constructor
  · apply (nativeBasis).ext
    intro index
    simp only [Module.End.mul_apply, P_basis, LinearMap.zero_apply]
    by_cases zero : nativeOccupation D xAxis yAxis index = 0
    · rw [if_pos zero, one_smul, nativeCoefficientBasis_as_signed, map_smul,
        original_delta_zero_occupation D frame xAxis yAxis xDual index.1.1 index.1.2 1
          (toggleOne index.2) zero coefficient, smul_zero]
    · simp [zero]
  · apply (nativeBasis).ext
    intro index
    simp only [Module.End.mul_apply, P_basis, LinearMap.zero_apply]
    by_cases zero : nativeOccupation D xAxis yAxis index = 0
    · rw [if_pos zero, one_smul, nativeCoefficientBasis_as_signed, map_smul,
        original_R_zero_occupation D frame xAxis yAxis yDual index.1.1 index.1.2 1
          (toggleOne index.2) zero coefficient, smul_zero]
    · simp [zero]

include distinct xDual yDual nonzero in
theorem original_normalized_strong_contraction :
    leading * normalized + normalized * leading = 1 - projector ∧
      normalized * normalized = 0 ∧ normalized * projector = 0 ∧ projector * normalized = 0 ∧
      leading * projector = 0 ∧ projector * leading = 0 ∧
      nullHomotopy * projector = 0 ∧ projector * nullHomotopy = 0 := by
  have squares := original_delta_R_square_and_K_commute D frame xAxis yAxis distinct xDual yDual coefficient nonzero
  have commutations := original_delta_R_Kdagger_P_commutations D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual coefficient nonzero
  have vanishing := original_delta_R_P_zero D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis xDual yDual coefficient
  have anticommutator := delta_R_anticommutator D (frame xAxis) (frame yAxis)
    (by simpa using xDual xAxis) coefficient nonzero
  have inverseP := native_Kdagger_P_zero D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
  have pInverse := native_P_Kdagger_zero D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
  refine ⟨?_, ?_, ?_, ?_, vanishing.1, ?_, vanishing.2, ?_⟩
  · change leading * (nullHomotopy * inverseK) + (nullHomotopy * inverseK) * leading = _
    calc
      _ = leading * nullHomotopy * inverseK + nullHomotopy * (inverseK * leading) := by noncomm_ring
      _ = (leading * nullHomotopy + nullHomotopy * leading) * inverseK := by
        rw [← commutations.1.1]
        noncomm_ring
      _ = _ := by
        rw [anticommutator, original_K_Kdagger D frame inverse leftFrameInverse rightFrameInverse
          xAxis yAxis xDual yDual]
  · change (nullHomotopy * inverseK) * (nullHomotopy * inverseK) = 0
    calc
      _ = nullHomotopy * (inverseK * nullHomotopy) * inverseK := by noncomm_ring
      _ = (nullHomotopy * nullHomotopy) * (inverseK * inverseK) := by
        rw [← commutations.2.1]
        noncomm_ring
      _ = 0 := by rw [squares.2.1, zero_mul]
  · change (nullHomotopy * inverseK) * projector = 0
    rw [mul_assoc, inverseP, mul_zero]
  · change projector * (nullHomotopy * inverseK) = 0
    rw [← mul_assoc, ← commutations.2.2, mul_assoc, pInverse, mul_zero]
  · rw [← commutations.1.2, vanishing.1]
  · rw [← commutations.2.2, vanishing.2]

include coefficient nonzero in
theorem original_K_B_zero_commutes : originalK * B D 0 = B D 0 * originalK := by
  have deltaB := original_delta_B_zero_anticommutes D (frame yAxis) coefficient
  have rB := original_R_B_zero_anticommutes D (frame xAxis) coefficient
  have anticommutator := delta_R_anticommutator D (frame xAxis) (frame yAxis)
    (by simpa using xDual xAxis) coefficient nonzero
  apply sub_eq_zero.mp
  calc
    _ = leading * (nullHomotopy * B D 0 + B D 0 * nullHomotopy) -
        (leading * B D 0 + B D 0 * leading) * nullHomotopy +
        nullHomotopy * (leading * B D 0 + B D 0 * leading) -
        (nullHomotopy * B D 0 + B D 0 * nullHomotopy) * leading := by
      rw [← anticommutator]
      noncomm_ring
    _ = 0 := by rw [deltaB, rB]; simp


include xDual yDual coefficient nonzero in
theorem original_Kdagger_P_B_zero_commute :
    B D 0 * inverseK = inverseK * B D 0 ∧ B D 0 * projector = projector * B D 0 := by
  exact native_commutations_of_K_commutation D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis xDual yDual (B D 0)
    (original_K_B_zero_commutes D frame xAxis yAxis xDual coefficient nonzero)

include xDual yDual nonzero in
theorem original_S_B_zero_anticommutes : normalized * B D 0 + B D 0 * normalized = 0 := by
  have commute := (original_Kdagger_P_B_zero_commute D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis xDual yDual coefficient nonzero).1
  change (nullHomotopy * inverseK) * B D 0 + B D 0 * (nullHomotopy * inverseK) = 0
  calc
    _ = nullHomotopy * (inverseK * B D 0) + (B D 0 * nullHomotopy) * inverseK := by noncomm_ring
    _ = (nullHomotopy * B D 0 + B D 0 * nullHomotopy) * inverseK := by
      rw [← commute]
      noncomm_ring
    _ = 0 := by rw [original_R_B_zero_anticommutes, zero_mul]

include xDual yDual nonzero in
theorem original_S_preserves_relative (state : State D) (relative : B D 0 state = 0) :
    B D 0 (normalized state) = 0 := by
  have equality := congrArg (fun operator : Module.End ℂ (State D) => operator state)
    (original_S_B_zero_anticommutes D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis xDual yDual coefficient nonzero)
  simpa only [LinearMap.add_apply, Module.End.mul_apply, relative, map_zero,
    zero_add, LinearMap.zero_apply] using equality

end Contraction

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
