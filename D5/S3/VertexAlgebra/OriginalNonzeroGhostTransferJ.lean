/- GID: D5/S3/VertexAlgebra/OriginalNonzeroGhostTransferJ
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual finite original-Q transfer is homogeneous for the native ghost grading.
-/

import D5.S3.VertexAlgebra.OriginalQActualQuotientTransferTransient

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge LatticeBcGhostBrstGhostNumber BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem J0_rAtom (D : LatticeData) (nullDirection : Fin D.rank → ℂ) (mode : ℤ) :
    J D * rAtom D nullDirection mode - rAtom D nullDirection mode * J D =
      -rAtom D nullDirection mode := by
  by_cases zeroMode : mode = 0
  · simp [rAtom, zeroMode]
  have ghostGrading : J D * B D mode - B D mode * J D = -B D mode := by
    have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
      (BcGhostNumber.J_b_commutator (K := ℂ) mode)
    simp only [map_sub, map_neg, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
    simpa only [J, B, LinearMap.lTensor_def, neg_smul] using lifted
  have matterCommute : J D * O D nullDirection (-mode) =
      O D nullDirection (-mode) * J D := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [J, O, Module.End.mul_apply]
  simp only [rAtom, if_neg zeroMode]
  calc
    _ = ((mode.natAbs : ℂ)⁻¹) •
        ((J D * O D nullDirection (-mode) - O D nullDirection (-mode) * J D) * B D mode +
          O D nullDirection (-mode) * (J D * B D mode - B D mode * J D)) := by
      simp only [smul_sub, smul_add, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, mul_assoc]
      abel
    _ = _ := by
      rw [matterCommute, ghostGrading, sub_self, zero_mul, zero_add]
      exact (congrArg (fun operator : Module.End ℂ (State D) => ((mode.natAbs : ℂ)⁻¹) • operator)
        (mul_neg (O D nullDirection (-mode)) (B D mode))).trans
        (smul_neg ((mode.natAbs : ℂ)⁻¹) (O D nullDirection (-mode) * B D mode))

theorem J0_rSum (D : LatticeData) (nullDirection : Fin D.rank → ℂ) :
    J D * rSum D nullDirection - rSum D nullDirection * J D = -rSum D nullDirection := by
  apply LinearMap.ext
  intro state
  have inputFinite := rAtom_finite D nullDirection state
  have outputFinite := rAtom_finite D nullDirection (J D state)
  have imageFinite := inputFinite.fun_comp (map_zero (J D))
  have mapped := (J D).toAddMonoidHom.map_finsum inputFinite
  simp only [LinearMap.toAddMonoidHom_coe] at mapped
  change J D (∑ᶠ mode : ℤ, rAtom D nullDirection mode state) -
    (∑ᶠ mode : ℤ, rAtom D nullDirection mode (J D state)) =
      -(∑ᶠ mode : ℤ, rAtom D nullDirection mode state)
  rw [mapped, ← finsum_sub_distrib imageFinite outputFinite]
  have negativeSum := smul_finsum' (-1 : ℂ) inputFinite
  simp only [neg_one_smul] at negativeSum
  rw [negativeSum]
  apply finsum_congr
  intro mode
  have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
    (J0_rAtom D nullDirection mode)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply] using operatorIdentity

theorem J0_R (D : LatticeData) (nullDirection : Fin D.rank → ℂ) (chargeCoefficient : ℂ) :
    J D * R D nullDirection chargeCoefficient - R D nullDirection chargeCoefficient * J D =
      -R D nullDirection chargeCoefficient := by
  have unscaled := J0_rSum D nullDirection
  simpa only [R, mul_smul_comm, smul_mul_assoc, smul_sub, smul_neg] using
    congrArg (fun operator : Module.End ℂ (State D) => chargeCoefficient⁻¹ • operator) unscaled

theorem J0_dAtom (D : LatticeData) (longitudinal : Fin D.rank → ℂ) (mode : ℤ) :
    J D * dAtom D longitudinal mode - dAtom D longitudinal mode * J D =
      dAtom D longitudinal mode := by
  by_cases zeroMode : mode = 0
  · simp [dAtom, zeroMode]
  have ghostGrading : J D * C D (-mode) - C D (-mode) * J D = C D (-mode) := by
    have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
      (BcGhostNumber.J_c_commutator (K := ℂ) (-mode))
    simp only [map_sub, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
    simpa only [J, C, LinearMap.lTensor_def] using lifted
  have matterCommute : J D * O D longitudinal mode = O D longitudinal mode * J D := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [J, O, Module.End.mul_apply]
  simp only [dAtom, if_neg zeroMode]
  calc
    _ = (J D * C D (-mode) - C D (-mode) * J D) * O D longitudinal mode +
        C D (-mode) * (J D * O D longitudinal mode - O D longitudinal mode * J D) := by
      simp only [mul_sub, sub_mul, mul_assoc]
      abel
    _ = _ := by rw [ghostGrading, matterCommute, sub_self]; simp

theorem J0_delta (D : LatticeData) (longitudinal : Fin D.rank → ℂ)
    (chargeCoefficient : ℂ) :
    J D * delta D longitudinal chargeCoefficient -
      delta D longitudinal chargeCoefficient * J D = delta D longitudinal chargeCoefficient := by
  have unscaled : J D * dSum D longitudinal - dSum D longitudinal * J D = dSum D longitudinal := by
    apply LinearMap.ext
    intro state
    have inputFinite := dAtom_finite D longitudinal state
    have outputFinite := dAtom_finite D longitudinal (J D state)
    have imageFinite := inputFinite.fun_comp (map_zero (J D))
    have mapped := (J D).toAddMonoidHom.map_finsum inputFinite
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change J D (∑ᶠ mode : ℤ, dAtom D longitudinal mode state) -
      (∑ᶠ mode : ℤ, dAtom D longitudinal mode (J D state)) = _
    rw [mapped, ← finsum_sub_distrib imageFinite outputFinite]
    apply finsum_congr
    intro mode
    have operatorIdentity := congrArg (fun operator : Module.End ℂ (State D) => operator state)
      (J0_dAtom D longitudinal mode)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply] using operatorIdentity
  simpa only [delta, mul_smul_comm, smul_mul_assoc, smul_sub] using
    congrArg (fun operator : Module.End ℂ (State D) => chargeCoefficient • operator) unscaled

theorem J0_nativeCoefficientBasis (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (index : NativeCoefficientIndex D) :
    J D (nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse index) =
      (BcGhostNumber.degree index.2 : ℂ) •
        nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse index := by
  rw [nativeCoefficientBasis_apply]
  simp only [J, LatticeBcGhostBrstGhostNumber.J, TensorProduct.map_tmul, LinearMap.id_apply]
  simp [BcGhostNumber.J, Finsupp.linearCombination_single, Finsupp.smul_single, smul_smul]
  rw [← TensorProduct.tmul_smul, Finsupp.smul_single]
  simp only [smul_eq_mul, mul_one]

theorem J0_Kdagger_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) :
    J D * Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis -
      Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis * J D = 0 := by
  classical
  apply (nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse).ext
  intro index
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    Kdagger_basis D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis index,
    J0_nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse index,
    map_smul, smul_smul, LinearMap.zero_apply]
  simp [smul_smul, mul_comm]

theorem J0_P_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) :
    J D * P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis -
      P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis * J D = 0 := by
  classical
  apply (nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse).ext
  intro index
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    P_basis D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis index,
    J0_nativeCoefficientBasis D frame inverse leftFrameInverse rightFrameInverse index,
    map_smul, smul_smul, LinearMap.zero_apply]
  simp [smul_smul, mul_comm]

theorem J0_S_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (coefficient : ℂ) :
    J D * S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis coefficient -
      S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis coefficient * J D =
      -S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis coefficient := by
  have inverseCommute := J0_Kdagger_commutator D frame inverse leftFrameInverse
    rightFrameInverse xAxis yAxis
  have rawDegree := J0_R D (frame xAxis) coefficient
  dsimp [S]
  calc
    _ = (J D * R D (frame xAxis) coefficient - R D (frame xAxis) coefficient * J D) *
          Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis +
        R D (frame xAxis) coefficient *
          (J D * Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis -
            Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis * J D) := by
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    _ = _ := by
      rw [rawDegree, inverseCommute, mul_zero, add_zero]
      exact neg_mul (R D (frame xAxis) coefficient)
        (Kdagger D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis)

theorem J0_Delta_commutator (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (longitudinal : Fin D.rank → ℂ) (chargeCoefficient : ℂ) :
    J D * (Q D H - delta D longitudinal chargeCoefficient) -
      (Q D H - delta D longitudinal chargeCoefficient) * J D =
      Q D H - delta D longitudinal chargeCoefficient := by
  have originalLaw := J_Q_commutator D H
  have leadingLaw := J0_delta D longitudinal chargeCoefficient
  calc
    _ = (J D * Q D H - Q D H * J D) -
        (J D * delta D longitudinal chargeCoefficient -
          delta D longitudinal chargeCoefficient * J D) := by
      simp only [mul_sub, sub_mul]
      abel
    _ = _ := by rw [originalLaw, leadingLaw]

theorem J0_chargeProjection_commutator (D : LatticeData) (beta : Charge D) :
    J D * chargeProjection D beta - chargeProjection D beta * J D = 0 := by
  apply TensorProduct.ext'
  intro matter ghost
  simp [J, chargeProjection, chargeEmbedding, chargeExtraction,
    LinearMap.comp_apply, TensorProduct.map_tmul, Finsupp.lsingle, Finsupp.lapply]

theorem J0_totalZero_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    J D * (M D H 0 + G D 0) - (M D H 0 + G D 0) * J D = 0 := by
  have matter : J D * M D H 0 - M D H 0 * J D = 0 := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [J, M, Module.End.mul_apply]
  have ghost : J D * G D 0 - G D 0 * J D = 0 := by
    have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
      (BcGhostNumber.J_L_commutator (K := ℂ) 0)
    simp only [map_sub, map_zero, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
    simpa only [J, G, LinearMap.lTensor_def] using lifted
  calc
    _ = (J D * M D H 0 - M D H 0 * J D) +
        (J D * G D 0 - G D 0 * J D) := by
      noncomm_ring
    _ = 0 := by rw [matter, ghost, add_zero]

theorem J0_product_commutator (D : LatticeData)
    (homotopy differential : Module.End ℂ (State D))
    (homotopyLaw : J D * homotopy - homotopy * J D = -homotopy)
    (differentialLaw : J D * differential - differential * J D = differential) :
    J D * (homotopy * differential) - (homotopy * differential) * J D = 0 := by
  have homotopy' := sub_eq_iff_eq_add.mp homotopyLaw
  have differential' := sub_eq_iff_eq_add.mp differentialLaw
  apply sub_eq_zero.mpr
  calc
    J D * (homotopy * differential) = (J D * homotopy) * differential := by
      simp only [mul_assoc]
    _ = (-homotopy + homotopy * J D) * differential := by rw [homotopy']
    _ = -(homotopy * differential) + homotopy * (J D * differential) := by
      noncomm_ring
      rw [smul_mul_assoc]
      abel
    _ = -(homotopy * differential) +
        homotopy * (differential + differential * J D) := by rw [differential']
    _ = (homotopy * differential) * J D := by
      noncomm_ring

theorem J0_product_degree_one_left (D : LatticeData)
    (left right : Module.End ℂ (State D))
    (leftLaw : J D * left - left * J D = left)
    (rightLaw : J D * right - right * J D = 0) :
    J D * (left * right) - (left * right) * J D = left * right := by
  have left' := sub_eq_iff_eq_add.mp leftLaw
  have right' := sub_eq_zero.mp rightLaw
  apply sub_eq_iff_eq_add.mpr
  calc
    J D * (left * right) = (J D * left) * right := by simp only [mul_assoc]
    _ = (left + left * J D) * right := by rw [left']
    _ = left * right + (left * J D) * right := by rw [add_mul]
    _ = left * right + left * (J D * right) := by rw [mul_assoc]
    _ = left * right + left * (right * J D) := by rw [right']
    _ = left * right + (left * right) * J D := by rw [mul_assoc]

theorem J0_product_degree_one_right (D : LatticeData)
    (left right : Module.End ℂ (State D))
    (leftLaw : J D * left - left * J D = 0)
    (rightLaw : J D * right - right * J D = right) :
    J D * (left * right) - (left * right) * J D = left * right := by
  have left' := sub_eq_zero.mp leftLaw
  have right' := sub_eq_iff_eq_add.mp rightLaw
  apply sub_eq_iff_eq_add.mpr
  calc
    J D * (left * right) = (J D * left) * right := by simp only [mul_assoc]
    _ = (left * J D) * right := by rw [left']
    _ = left * (J D * right) := by rw [mul_assoc]
    _ = left * (right + right * J D) := by rw [right']
    _ = left * right + left * (right * J D) := by rw [mul_add]
    _ = left * right + (left * right) * J D := by rw [mul_assoc]

theorem J0_correction_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
    (xAxis yAxis : Fin D.rank) :
    J D *
        (S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
            (chosenP D beta nullDirection) *
          (Q D H - delta D (adaptedPartner D beta nullDirection)
            (chosenP D beta nullDirection))) -
    (S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
          (chosenP D beta nullDirection) *
        (Q D H - delta D (adaptedPartner D beta nullDirection)
          (chosenP D beta nullDirection))) * J D = 0 := by
  exact J0_product_commutator D
    (S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
      (chosenP D beta nullDirection))
    (Q D H - delta D (adaptedPartner D beta nullDirection)
      (chosenP D beta nullDirection))
    (J0_S_commutator D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
      (chosenP D beta nullDirection))
    (J0_Delta_commutator D H (adaptedPartner D beta nullDirection)
      (chosenP D beta nullDirection))

theorem J0_correction_power_commutator (D : LatticeData)
    (operator : Module.End ℂ (State D)) (hoperator : J D * operator - operator * J D = 0)
    (steps : ℕ) : J D * operator ^ steps - operator ^ steps * J D = 0 := by
  have commute : J D * operator = operator * J D := sub_eq_zero.mp hoperator
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [pow_succ]
      have powerCommute : J D * operator ^ steps = operator ^ steps * J D :=
        sub_eq_zero.mp inductionHypothesis
      apply sub_eq_zero.mpr
      calc
        J D * (operator ^ steps * operator) = (J D * operator ^ steps) * operator := by
          simp only [mul_assoc]
        _ = (operator ^ steps * J D) * operator := by rw [powerCommute]
        _ = operator ^ steps * (J D * operator) := by simp only [mul_assoc]
        _ = operator ^ steps * (operator * J D) := by rw [commute]
        _ = (operator ^ steps * operator) * J D := by simp only [mul_assoc]

theorem J0_finite_correction_inverse_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
    (xAxis yAxis : Fin D.rank) (level : ℤ) :
    J D * finiteOriginalCorrectionInverse D H frame inverse leftFrameInverse rightFrameInverse
        beta nullDirection xAxis yAxis level -
      finiteOriginalCorrectionInverse D H frame inverse leftFrameInverse rightFrameInverse
        beta nullDirection xAxis yAxis level * J D = 0 := by
  let correction := S D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
      (chosenP D beta nullDirection) *
    (Q D H - delta D (adaptedPartner D beta nullDirection) (chosenP D beta nullDirection))
  have correctionCommute : J D * correction - correction * J D = 0 := by
    exact J0_correction_commutator D H frame inverse leftFrameInverse rightFrameInverse beta
      nullDirection xAxis yAxis
  change J D * (∑ steps ∈ Finset.range (2 * level.toNat + 2), (-correction) ^ steps) -
    (∑ steps ∈ Finset.range (2 * level.toNat + 2), (-correction) ^ steps) * J D = 0
  have negCorrectionCommute : J D * (-correction) - (-correction) * J D = 0 := by
    rw [show -correction = (-1 : ℂ) • correction by
      exact (neg_one_smul ℂ correction).symm]
    rw [mul_smul_comm, smul_mul_assoc]
    have scaled := congrArg (fun operator : Module.End ℂ (State D) =>
        (-1 : ℂ) • operator) correctionCommute
    simpa only [smul_sub, smul_zero] using scaled
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro steps stepsMember
  exact J0_correction_power_commutator D (-correction) negCorrectionCommute steps

theorem J0_finite_transferred_differential_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
    (xAxis yAxis : Fin D.rank) (level : ℤ) :
    J D * finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
        beta nullDirection xAxis yAxis level -
      finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
        beta nullDirection xAxis yAxis level * J D =
      finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
        beta nullDirection xAxis yAxis level := by
  let projector := P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
  let differential := Q D H - delta D (adaptedPartner D beta nullDirection)
    (chosenP D beta nullDirection)
  let inverseOperator := finiteOriginalCorrectionInverse D H frame inverse leftFrameInverse
    rightFrameInverse beta nullDirection xAxis yAxis level
  have projectorLaw : J D * projector - projector * J D = 0 := by
    exact J0_P_commutator D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis
  have differentialLaw : J D * differential - differential * J D = differential := by
    exact J0_Delta_commutator D H (adaptedPartner D beta nullDirection)
      (chosenP D beta nullDirection)
  have inverseLaw : J D * inverseOperator - inverseOperator * J D = 0 := by
    exact J0_finite_correction_inverse_commutator D H frame inverse leftFrameInverse
      rightFrameInverse beta nullDirection xAxis yAxis level
  change J D * (projector * differential * inverseOperator * projector) -
    (projector * differential * inverseOperator * projector) * J D =
      projector * differential * inverseOperator * projector
  have first := J0_product_degree_one_right D projector differential projectorLaw differentialLaw
  have second := J0_product_degree_one_left D (projector * differential) inverseOperator first inverseLaw
  exact J0_product_degree_one_left D (projector * differential * inverseOperator) projector second projectorLaw

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
