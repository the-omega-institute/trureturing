import D5.S3.VertexAlgebra.TemporaryNativeContraction19
import D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge LatticeBcGhostBrstGhostNumber BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

section RawHomotopy

theorem J0_rAtom (D : LatticeData) (nullDirection : Fin D.rank → ℂ) (mode : ℤ) :
    LatticeBcGhostBrstGhostNumber.J D * rAtom D nullDirection mode -
      rAtom D nullDirection mode * LatticeBcGhostBrstGhostNumber.J D =
      -rAtom D nullDirection mode := by
  by_cases zeroMode : mode = 0
  · simp [rAtom, zeroMode]
  have ghostGrading :
      LatticeBcGhostBrstGhostNumber.J D * B D mode -
        B D mode * LatticeBcGhostBrstGhostNumber.J D = -B D mode := by
    have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
      (BcGhostNumber.J_b_commutator (K := ℂ) mode)
    simp only [map_sub, map_neg, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
    simpa only [LatticeBcGhostBrstGhostNumber.J, B, LinearMap.lTensor_def,
      neg_smul] using lifted
  have matterCommute :
      LatticeBcGhostBrstGhostNumber.J D * O D nullDirection (-mode) =
        O D nullDirection (-mode) * LatticeBcGhostBrstGhostNumber.J D := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [LatticeBcGhostBrstGhostNumber.J, O, Module.End.mul_apply]
  simp only [rAtom, if_neg zeroMode]
  calc
    _ = ((mode.natAbs : ℂ)⁻¹) •
        ((LatticeBcGhostBrstGhostNumber.J D * O D nullDirection (-mode) -
            O D nullDirection (-mode) * LatticeBcGhostBrstGhostNumber.J D) *
          B D mode +
          O D nullDirection (-mode) *
            (LatticeBcGhostBrstGhostNumber.J D * B D mode -
              B D mode * LatticeBcGhostBrstGhostNumber.J D)) := by
      simp only [smul_sub, smul_add, smul_mul_assoc, mul_smul_comm,
        sub_mul, mul_sub, mul_assoc]
      abel
    _ = _ := by
      rw [matterCommute, ghostGrading, sub_self, zero_mul, zero_add]
      exact (congrArg (fun operator : Module.End ℂ (State D) =>
        ((mode.natAbs : ℂ)⁻¹) • operator)
        (mul_neg (O D nullDirection (-mode)) (B D mode))).trans
        (smul_neg ((mode.natAbs : ℂ)⁻¹) (O D nullDirection (-mode) * B D mode))

theorem J0_rSum (D : LatticeData) (nullDirection : Fin D.rank → ℂ) :
    LatticeBcGhostBrstGhostNumber.J D * rSum D nullDirection -
      rSum D nullDirection * LatticeBcGhostBrstGhostNumber.J D =
      -rSum D nullDirection := by
  apply LinearMap.ext
  intro state
  have inputFinite := rAtom_finite D nullDirection state
  have outputFinite := rAtom_finite D nullDirection
    (LatticeBcGhostBrstGhostNumber.J D state)
  have imageFinite := inputFinite.fun_comp (map_zero (LatticeBcGhostBrstGhostNumber.J D))
  have mapped := (LatticeBcGhostBrstGhostNumber.J D).toAddMonoidHom.map_finsum inputFinite
  simp only [LinearMap.toAddMonoidHom_coe] at mapped
  change LatticeBcGhostBrstGhostNumber.J D
      (∑ᶠ mode : ℤ, rAtom D nullDirection mode state) -
      (∑ᶠ mode : ℤ,
        rAtom D nullDirection mode (LatticeBcGhostBrstGhostNumber.J D state)) =
      -(∑ᶠ mode : ℤ, rAtom D nullDirection mode state)
  rw [mapped, ← finsum_sub_distrib imageFinite outputFinite]
  have negativeSum := smul_finsum' (-1 : ℂ) inputFinite
  simp only [neg_one_smul] at negativeSum
  rw [negativeSum]
  apply finsum_congr
  intro mode
  have operatorIdentity := congrArg
    (fun operator : Module.End ℂ (State D) => operator state)
    (J0_rAtom D nullDirection mode)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply] using operatorIdentity

theorem J0_R (D : LatticeData) (nullDirection : Fin D.rank → ℂ)
    (chargeCoefficient : ℂ) :
    LatticeBcGhostBrstGhostNumber.J D * R D nullDirection chargeCoefficient -
      R D nullDirection chargeCoefficient * LatticeBcGhostBrstGhostNumber.J D =
      -R D nullDirection chargeCoefficient := by
  have unscaled := J0_rSum D nullDirection
  simpa only [R, mul_smul_comm, smul_mul_assoc, smul_sub, smul_neg] using
    congrArg (fun operator : Module.End ℂ (State D) => chargeCoefficient⁻¹ • operator)
      unscaled

end RawHomotopy

section NativeBasis

variable (D : LatticeData)
  (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftFrameInverse : inverse * frame = 1)
  (rightFrameInverse : frame * inverse = 1)

local notation "nativeBasis" =>
  nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse

theorem J0_nativeCoefficientBasis (index : NativeCoefficientIndex D) :
    LatticeBcGhostBrstGhostNumber.J D (nativeBasis index) =
      (BcGhostNumber.degree index.2 : ℂ) • nativeBasis index := by
  rw [nativeCoefficientBasis_apply]
  simp only [LatticeBcGhostBrstGhostNumber.J, TensorProduct.map_tmul, LinearMap.id_apply]
  simp [BcGhostNumber.J, Finsupp.linearCombination_single, Finsupp.smul_single,
    smul_smul]
  rw [← TensorProduct.tmul_smul, Finsupp.smul_single]
  simp only [smul_eq_mul, mul_one]

theorem J0_Kdagger_commutator (xAxis yAxis : Fin D.rank) :
    LatticeBcGhostBrstGhostNumber.J D *
        Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis -
      Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis *
        LatticeBcGhostBrstGhostNumber.J D = 0 := by
  classical
  apply (nativeBasis).ext
  intro index
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    Kdagger_basis D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis index,
    J0_nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse index,
    map_smul, smul_smul, LinearMap.zero_apply]
  simp [smul_smul, mul_comm]

theorem J0_P_commutator (xAxis yAxis : Fin D.rank) :
    LatticeBcGhostBrstGhostNumber.J D *
        P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis -
      P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis *
        LatticeBcGhostBrstGhostNumber.J D = 0 := by
  classical
  apply (nativeBasis).ext
  intro index
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    P_basis D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis index,
    J0_nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse index,
    map_smul, smul_smul, LinearMap.zero_apply]
  simp [smul_smul, mul_comm]

theorem J0_originalK_commutator (xAxis yAxis : Fin D.rank)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) =
      if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) =
      if row = yAxis then 1 else 0) :
    LatticeBcGhostBrstGhostNumber.J D *
        K D (frame xAxis) (frame yAxis) (by simpa using xDual xAxis) -
      K D (frame xAxis) (frame yAxis) (by simpa using xDual xAxis) *
        LatticeBcGhostBrstGhostNumber.J D = 0 := by
  let grading := LatticeBcGhostBrstGhostNumber.J D
  let leading := delta D (frame yAxis) (1 : ℂ)
  let homotopy := R D (frame xAxis) (1 : ℂ)
  have leadingGrade := J_delta D (frame yAxis) (1 : ℂ)
  have homotopyGrade := J0_R D (frame xAxis) (1 : ℂ)
  have factorization := delta_R_anticommutator D (frame xAxis) (frame yAxis)
    (by simpa using xDual xAxis) (1 : ℂ) one_ne_zero
  change grading * leading - leading * grading = leading at leadingGrade
  change grading * homotopy - homotopy * grading = -homotopy at homotopyGrade
  change leading * homotopy + homotopy * leading = _ at factorization
  change grading * K D (frame xAxis) (frame yAxis) _ -
    K D (frame xAxis) (frame yAxis) _ * grading = 0
  rw [← factorization]
  calc
    _ = ((grading * leading - leading * grading) * homotopy +
        leading * (grading * homotopy - homotopy * grading)) +
        ((grading * homotopy - homotopy * grading) * leading +
          homotopy * (grading * leading - leading * grading)) := by
      simp only [mul_add, add_mul, sub_mul, mul_sub, mul_assoc]
      abel
    _ = 0 := by
      simp only [leadingGrade, homotopyGrade,
        mul_neg leading homotopy, neg_mul homotopy leading]
      abel

end NativeBasis

section NormalizedHomotopy

variable (D : LatticeData)
  (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftFrameInverse : inverse * frame = 1)
  (rightFrameInverse : frame * inverse = 1)
  (xAxis yAxis : Fin D.rank) (chargeCoefficient : ℂ)

theorem J0_S :
    LatticeBcGhostBrstGhostNumber.J D *
        S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis chargeCoefficient -
      S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis chargeCoefficient *
        LatticeBcGhostBrstGhostNumber.J D =
      -S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis chargeCoefficient := by
  have inverseCommute := J0_Kdagger_commutator D frame inverse leftFrameInverse
    rightFrameInverse xAxis yAxis
  have rawDegree := J0_R D (frame xAxis) chargeCoefficient
  dsimp [S]
  calc
    _ = (LatticeBcGhostBrstGhostNumber.J D * R D (frame xAxis) chargeCoefficient -
        R D (frame xAxis) chargeCoefficient * LatticeBcGhostBrstGhostNumber.J D) *
          Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis +
        R D (frame xAxis) chargeCoefficient *
          (LatticeBcGhostBrstGhostNumber.J D *
              Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis -
            Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis *
              LatticeBcGhostBrstGhostNumber.J D) := by
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    _ = _ := by
      rw [rawDegree, inverseCommute, mul_zero, add_zero]
      exact neg_mul (R D (frame xAxis) chargeCoefficient)
        (Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis)

end NormalizedHomotopy

section OriginalCharge

theorem J0_Delta (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (longitudinal : Fin D.rank → ℂ) (chargeCoefficient : ℂ) :
    LatticeBcGhostBrstGhostNumber.J D *
        (Q D H - delta D longitudinal chargeCoefficient) -
      (Q D H - delta D longitudinal chargeCoefficient) *
        LatticeBcGhostBrstGhostNumber.J D =
      Q D H - delta D longitudinal chargeCoefficient := by
  have originalLaw := LatticeBcGhostBrstGhostNumber.J_Q_commutator D H
  have leadingLaw := J_delta D longitudinal chargeCoefficient
  calc
    _ = (LatticeBcGhostBrstGhostNumber.J D * Q D H -
          Q D H * LatticeBcGhostBrstGhostNumber.J D) -
        (LatticeBcGhostBrstGhostNumber.J D * delta D longitudinal chargeCoefficient -
          delta D longitudinal chargeCoefficient * LatticeBcGhostBrstGhostNumber.J D) := by
      simp only [mul_sub, sub_mul]
      abel
    _ = _ := by rw [originalLaw, leadingLaw]

theorem J0_native_HPL_grade_data (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (chargeCoefficient : ℂ)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (longitudinal : Fin D.rank → ℂ) :
    (LatticeBcGhostBrstGhostNumber.J D * delta D longitudinal chargeCoefficient -
        delta D longitudinal chargeCoefficient * LatticeBcGhostBrstGhostNumber.J D =
      delta D longitudinal chargeCoefficient) ∧
    (LatticeBcGhostBrstGhostNumber.J D *
        S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis chargeCoefficient -
      S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis chargeCoefficient *
        LatticeBcGhostBrstGhostNumber.J D =
      -S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis chargeCoefficient) ∧
    (LatticeBcGhostBrstGhostNumber.J D *
        P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis =
      P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis *
        LatticeBcGhostBrstGhostNumber.J D) ∧
    (LatticeBcGhostBrstGhostNumber.J D *
        (Q D H - delta D longitudinal chargeCoefficient) -
      (Q D H - delta D longitudinal chargeCoefficient) *
        LatticeBcGhostBrstGhostNumber.J D =
      Q D H - delta D longitudinal chargeCoefficient) ∧
    (LatticeBcGhostBrstGhostNumber.J D * Q D H -
      Q D H * LatticeBcGhostBrstGhostNumber.J D = Q D H) := by
  refine ⟨J_delta D longitudinal chargeCoefficient,
    J0_S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis chargeCoefficient,
    ?_, J0_Delta D H longitudinal chargeCoefficient,
    LatticeBcGhostBrstGhostNumber.J_Q_commutator D H⟩
  exact sub_eq_zero.mp
    (J0_P_commutator D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis)

end OriginalCharge

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
