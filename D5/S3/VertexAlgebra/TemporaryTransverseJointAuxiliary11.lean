import D5.S3.VertexAlgebra.TemporaryTransverseJointAuxiliary10
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraVirasoro LatticeSugawaraConformal LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem auxiliary_dAtom_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (axis : Fin D.rank) (mode : ℤ) :
    auxiliary D frame inverse xAxis yAxis * dAtom D (frame axis) mode -
      dAtom D (frame axis) mode * auxiliary D frame inverse xAxis yAxis =
      ((axisAuxDegree D xAxis yAxis axis : ℂ) + 1) • dAtom D (frame axis) mode := by
  by_cases zeroMode : mode = 0
  · simp [dAtom, zeroMode]
  have cGrade := auxiliary_C_commutator D frame inverse xAxis yAxis (-mode)
  have oGrade := auxiliary_O_commutator D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual axis mode zeroMode
  simp only [dAtom, if_neg zeroMode]
  calc
    _ = (auxiliary D frame inverse xAxis yAxis * C D (-mode) - C D (-mode) * auxiliary D frame inverse xAxis yAxis) *
          O D (frame axis) mode + C D (-mode) *
        (auxiliary D frame inverse xAxis yAxis * O D (frame axis) mode -
          O D (frame axis) mode * auxiliary D frame inverse xAxis yAxis) := by
        simp only [sub_mul, mul_sub, add_mul, mul_add]
        noncomm_ring
    _ = _ := by rw [cGrade, oGrade]; simp [mul_smul_comm, add_smul, add_comm]

theorem auxiliary_dSum_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (axis : Fin D.rank) :
    auxiliary D frame inverse xAxis yAxis * dSum D (frame axis) -
      dSum D (frame axis) * auxiliary D frame inverse xAxis yAxis =
      ((axisAuxDegree D xAxis yAxis axis : ℂ) + 1) • dSum D (frame axis) := by
  apply LinearMap.ext
  intro state
  have inputFinite := dAtom_finite D (frame axis) state
  have auxiliaryFinite := dAtom_finite D (frame axis) (auxiliary D frame inverse xAxis yAxis state)
  have mappedFinite := inputFinite.fun_comp (map_zero (auxiliary D frame inverse xAxis yAxis))
  have mapped := (auxiliary D frame inverse xAxis yAxis).toAddMonoidHom.map_finsum inputFinite
  simp only [LinearMap.toAddMonoidHom_coe] at mapped
  change auxiliary D frame inverse xAxis yAxis (∑ᶠ mode : ℤ, dAtom D (frame axis) mode state) -
    (∑ᶠ mode : ℤ, dAtom D (frame axis) mode (auxiliary D frame inverse xAxis yAxis state)) =
    ((axisAuxDegree D xAxis yAxis axis : ℂ) + 1) • ∑ᶠ mode : ℤ, dAtom D (frame axis) mode state
  rw [mapped, ← finsum_sub_distrib mappedFinite auxiliaryFinite, smul_finsum' _ inputFinite]
  apply finsum_congr
  intro mode
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] using congrArg
    (fun operator : Module.End ℂ (State D) => operator state)
    (auxiliary_dAtom_commutator D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis distinct xDual yDual axis mode)

theorem auxiliary_delta_zero (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (coefficient : ℂ) :
    auxiliary D frame inverse xAxis yAxis * delta D (frame yAxis) coefficient -
      delta D (frame yAxis) coefficient * auxiliary D frame inverse xAxis yAxis = 0 := by
  have actual := auxiliary_dSum_commutator D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual yAxis
  have actual' : auxiliary D frame inverse xAxis yAxis * dSum D (frame yAxis) -
      dSum D (frame yAxis) * auxiliary D frame inverse xAxis yAxis = 0 := by
    simpa [axisAuxDegree, Ne.symm distinct] using actual
  have scaled := congrArg (fun operator : Module.End ℂ (State D) => coefficient • operator) actual'
  simpa only [delta, mul_smul_comm, smul_mul_assoc, smul_sub, smul_zero] using scaled

theorem auxiliary_rAtom_zero (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (mode : ℤ) :
    auxiliary D frame inverse xAxis yAxis * rAtom D (frame xAxis) mode -
      rAtom D (frame xAxis) mode * auxiliary D frame inverse xAxis yAxis = 0 := by
  by_cases zeroMode : mode = 0
  · simp [rAtom, zeroMode]
  have oppositeNonzero : -mode ≠ 0 := neg_ne_zero.mpr zeroMode
  have oGrade := auxiliary_O_commutator D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual xAxis (-mode) oppositeNonzero
  have oGrade' : auxiliary D frame inverse xAxis yAxis * O D (frame xAxis) (-mode) -
      O D (frame xAxis) (-mode) * auxiliary D frame inverse xAxis yAxis =
      O D (frame xAxis) (-mode) := by
    simpa [axisAuxDegree] using oGrade
  have bGrade := auxiliary_B_commutator D frame inverse xAxis yAxis mode
  have productGrade : auxiliary D frame inverse xAxis yAxis * (O D (frame xAxis) (-mode) * B D mode) -
      (O D (frame xAxis) (-mode) * B D mode) * auxiliary D frame inverse xAxis yAxis = 0 := by
    calc
      _ = (auxiliary D frame inverse xAxis yAxis * O D (frame xAxis) (-mode) -
            O D (frame xAxis) (-mode) * auxiliary D frame inverse xAxis yAxis) * B D mode +
          O D (frame xAxis) (-mode) * (auxiliary D frame inverse xAxis yAxis * B D mode -
            B D mode * auxiliary D frame inverse xAxis yAxis) := by
        simp only [sub_mul, mul_sub, add_mul, mul_add]
        noncomm_ring
      _ = _ := by
        rw [oGrade', bGrade]
        exact (congrArg (fun operator : Module.End ℂ (State D) =>
          O D (frame xAxis) (-mode) * B D mode + operator)
          (mul_neg (O D (frame xAxis) (-mode)) (B D mode))).trans
          (add_neg_cancel (O D (frame xAxis) (-mode) * B D mode))
  have scaled := congrArg (fun operator : Module.End ℂ (State D) =>
      (mode.natAbs : ℂ)⁻¹ • operator) productGrade
  simpa only [rAtom, if_neg zeroMode, mul_smul_comm, smul_mul_assoc, smul_sub, smul_zero] using scaled

theorem auxiliary_R_zero (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (coefficient : ℂ) :
    auxiliary D frame inverse xAxis yAxis * R D (frame xAxis) coefficient -
      R D (frame xAxis) coefficient * auxiliary D frame inverse xAxis yAxis = 0 := by
  have summed : auxiliary D frame inverse xAxis yAxis * rSum D (frame xAxis) -
      rSum D (frame xAxis) * auxiliary D frame inverse xAxis yAxis = 0 := by
    apply LinearMap.ext
    intro state
    have inputFinite := rAtom_finite D (frame xAxis) state
    have auxiliaryFinite := rAtom_finite D (frame xAxis) (auxiliary D frame inverse xAxis yAxis state)
    have imageFinite := inputFinite.fun_comp (map_zero (auxiliary D frame inverse xAxis yAxis))
    have mapped := (auxiliary D frame inverse xAxis yAxis).toAddMonoidHom.map_finsum inputFinite
    simp only [LinearMap.toAddMonoidHom_coe] at mapped
    change auxiliary D frame inverse xAxis yAxis (∑ᶠ mode : ℤ, rAtom D (frame xAxis) mode state) -
      (∑ᶠ mode : ℤ, rAtom D (frame xAxis) mode (auxiliary D frame inverse xAxis yAxis state)) = 0
    rw [mapped, ← finsum_sub_distrib imageFinite auxiliaryFinite]
    have termZero (mode : ℤ) := congrArg (fun operator : Module.End ℂ (State D) => operator state)
      (auxiliary_rAtom_zero D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis distinct xDual yDual mode)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at termZero
    simp_rw [termZero]
    exact finsum_zero
  have scaled := congrArg (fun operator : Module.End ℂ (State D) => coefficient⁻¹ • operator) summed
  simpa only [R, mul_smul_comm, smul_mul_assoc, smul_sub, smul_zero] using scaled

def raisingOneAtom (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ) (mode : ℤ) : Module.End ℂ (State D) :=
  A D H mode - chosenP D charge nullDirection • dAtom D (adaptedPartner D charge nullDirection) mode -
    chosenQ D charge nullDirection • dAtom D nullDirection mode

def raisingOne (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ) : Module.End ℂ (State D) :=
  Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection) -
    chosenQ D charge nullDirection • dSum D nullDirection

def raisingTwo (D : LatticeData) (charge : Charge D) (nullDirection : Fin D.rank → ℂ) :
    Module.End ℂ (State D) := chosenQ D charge nullDirection • dSum D nullDirection

theorem raisingOneAtom_finite (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ) (state : State D) :
    Function.HasFiniteSupport (fun mode : ℤ => raisingOneAtom D H charge nullDirection mode state) := by
  have firstFinite := (dAtom_finite D (adaptedPartner D charge nullDirection) state).fun_comp
    (show chosenP D charge nullDirection • (0 : State D) = 0 by simp)
  have secondFinite := (dAtom_finite D nullDirection state).fun_comp
    (show chosenQ D charge nullDirection • (0 : State D) = 0 by simp)
  change Function.HasFiniteSupport
    ((fun mode : ℤ => A D H mode state) -
      (fun mode : ℤ => chosenP D charge nullDirection •
        dAtom D (adaptedPartner D charge nullDirection) mode state) -
      (fun mode : ℤ => chosenQ D charge nullDirection • dAtom D nullDirection mode state))
  exact ((A_finite D H state).sub firstFinite).sub secondFinite

theorem raisingOne_actual_finsum (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ) (state : State D) :
    raisingOne D H charge nullDirection state = ∑ᶠ mode : ℤ, raisingOneAtom D H charge nullDirection mode state := by
  have firstFinite := (dAtom_finite D (adaptedPartner D charge nullDirection) state).fun_comp
    (show chosenP D charge nullDirection • (0 : State D) = 0 by simp)
  have secondFinite := (dAtom_finite D nullDirection state).fun_comp
    (show chosenQ D charge nullDirection • (0 : State D) = 0 by simp)
  change ((∑ᶠ mode : ℤ, A D H mode state) - chosenP D charge nullDirection •
      (∑ᶠ mode : ℤ, dAtom D (adaptedPartner D charge nullDirection) mode state)) -
    chosenQ D charge nullDirection • (∑ᶠ mode : ℤ, dAtom D nullDirection mode state) = _
  rw [smul_finsum' _ (dAtom_finite D (adaptedPartner D charge nullDirection) state),
    smul_finsum' _ (dAtom_finite D nullDirection state)]
  have hs1 : (∑ᶠ mode : ℤ, A D H mode state) -
      ∑ᶠ mode : ℤ, chosenP D charge nullDirection •
        (dAtom D (adaptedPartner D charge nullDirection) mode state) =
      ∑ᶠ mode : ℤ, (A D H mode state - chosenP D charge nullDirection •
        dAtom D (adaptedPartner D charge nullDirection) mode state) := by
    simpa only [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply'] using
      (finsum_sub_distrib (A_finite D H state) firstFinite).symm
  have hs2 : (∑ᶠ mode : ℤ, (A D H mode state - chosenP D charge nullDirection •
        dAtom D (adaptedPartner D charge nullDirection) mode state)) -
      ∑ᶠ mode : ℤ, chosenQ D charge nullDirection • dAtom D nullDirection mode state =
      ∑ᶠ mode : ℤ, ((A D H mode state - chosenP D charge nullDirection •
        dAtom D (adaptedPartner D charge nullDirection) mode state) -
        chosenQ D charge nullDirection • dAtom D nullDirection mode state) := by
    simpa only [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply'] using
      (finsum_sub_distrib ((A_finite D H state).sub firstFinite) secondFinite).symm
  rw [hs1, hs2]
  rfl

theorem raisingOneAtom_nonzero_native (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D charge nullDirection ≠ 0)
    (mode : ℤ) (nonzeroMode : mode ≠ 0) (polynomial : Oscillator D) (ghost : Fock ℂ) :
    raisingOneAtom D H charge nullDirection mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) =
      (C D (-mode) * oscillatorLift D H mode + (2 : ℂ)⁻¹ • N D mode)
        (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) := by
  have original := original_A_leading_piece D H leftGramInverse rightGramInverse charge
    nullDirection null nonzero polynomial ghost mode nonzeroMode
  simp only [raisingOneAtom, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [original]
  simp only [dAtom, if_neg nonzeroMode, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, oscillatorLift, TensorProduct.map_tmul, LinearMap.id_apply]
  abel

theorem raisingOneAtom_aux_degree_one (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D charge nullDirection ≠ 0)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (mode : ℤ) (polynomial : Oscillator D) (ghost : Fock ℂ) :
    auxiliary D frame inverse xAxis yAxis
        (raisingOneAtom D H charge nullDirection mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) -
      raisingOneAtom D H charge nullDirection mode
        (auxiliary D frame inverse xAxis yAxis (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) =
      raisingOneAtom D H charge nullDirection mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) := by
  by_cases zeroMode : mode = 0
  · subst mode
    have original := congrArg (fun operator : Module.End ℂ (State D) =>
      operator (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost))
      (auxiliary_A_zero_commutator D H frame inverse leftGramInverse rightGramInverse
        leftFrameInverse rightFrameInverse xAxis yAxis)
    simpa [raisingOneAtom, dAtom] using original
  let remaining : Module.End ℂ (State D) := C D (-mode) * oscillatorLift D H mode + (2 : ℂ)⁻¹ • N D mode
  have same (input : Oscillator D) (inputGhost : Fock ℂ) :
      raisingOneAtom D H charge nullDirection mode (Finsupp.single charge input ⊗ₜ[ℂ] inputGhost) =
        remaining (Finsupp.single charge input ⊗ₜ[ℂ] inputGhost) :=
    raisingOneAtom_nonzero_native D H leftGramInverse rightGramInverse charge nullDirection null nonzero
      mode zeroMode input inputGhost
  have sameAux : raisingOneAtom D H charge nullDirection mode
      (auxiliary D frame inverse xAxis yAxis (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) =
      remaining (auxiliary D frame inverse xAxis yAxis (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) := by
    simp only [auxiliary, LinearMap.sub_apply, LinearMap.add_apply, matterAuxLift,
      TensorProduct.map_tmul, LinearMap.id_apply, matterAux_single, LatticeBcGhostBrstGhostNumber.J,
      Module.End.one_apply, map_sub, map_add]
    simp only [same]
  have cGrade := auxiliary_C_commutator D frame inverse xAxis yAxis (-mode)
  have quadraticGrade := auxiliary_oscillator_commutator D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse xAxis yAxis distinct xDual yDual mode
  have nGrade := auxiliary_N_commutator D frame inverse xAxis yAxis mode
  have remainingGrade : auxiliary D frame inverse xAxis yAxis * remaining -
      remaining * auxiliary D frame inverse xAxis yAxis = remaining := by
    dsimp [remaining]
    calc
      _ = (auxiliary D frame inverse xAxis yAxis * C D (-mode) - C D (-mode) * auxiliary D frame inverse xAxis yAxis) *
            oscillatorLift D H mode + C D (-mode) *
          (auxiliary D frame inverse xAxis yAxis * oscillatorLift D H mode -
            oscillatorLift D H mode * auxiliary D frame inverse xAxis yAxis) +
          (2 : ℂ)⁻¹ • (auxiliary D frame inverse xAxis yAxis * N D mode -
            N D mode * auxiliary D frame inverse xAxis yAxis) := by
        simp only [mul_add, add_mul, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, smul_sub,
          neg_smul]
        noncomm_ring
      _ = _ := by rw [cGrade, quadraticGrade, nGrade]; simp
  simp only [same, sameAux]
  simpa only [LinearMap.sub_apply, Module.End.mul_apply] using congrArg
    (fun operator : Module.End ℂ (State D) => operator (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost))
    remainingGrade

theorem raisingOne_aux_degree_one_tmul (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D charge nullDirection ≠ 0)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (polynomial : Oscillator D) (ghost : Fock ℂ) :
    auxiliary D frame inverse xAxis yAxis
        (raisingOne D H charge nullDirection (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) -
      raisingOne D H charge nullDirection
        (auxiliary D frame inverse xAxis yAxis (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) =
      raisingOne D H charge nullDirection (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) := by
  let state := Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost
  have inputFinite := raisingOneAtom_finite D H charge nullDirection state
  have auxiliaryFinite := raisingOneAtom_finite D H charge nullDirection (auxiliary D frame inverse xAxis yAxis state)
  have imageFinite := inputFinite.fun_comp (map_zero (auxiliary D frame inverse xAxis yAxis))
  have mapped := (auxiliary D frame inverse xAxis yAxis).toAddMonoidHom.map_finsum inputFinite
  simp only [LinearMap.toAddMonoidHom_coe] at mapped
  simp only [raisingOne_actual_finsum]
  rw [mapped, ← finsum_sub_distrib imageFinite auxiliaryFinite]
  apply finsum_congr
  intro mode
  exact raisingOneAtom_aux_degree_one D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse charge nullDirection null nonzero xAxis yAxis distinct xDual yDual
    mode polynomial ghost

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
