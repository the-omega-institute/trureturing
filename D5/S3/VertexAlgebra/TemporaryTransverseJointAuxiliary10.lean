import D5.S3.VertexAlgebra.TemporaryTransverseJointAuxiliary09
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraVirasoro LatticeSugawaraConformal LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def oscillatorLift (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) :
    Module.End ℂ (State D) := TensorProduct.map (oscillatorSugawaraMode D H mode) LinearMap.id

theorem matterAux_frameOscillatorNormal (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (first second : Fin D.rank) (mode internal : ℤ) :
    matterAux D frame inverse xAxis yAxis * frameOscillatorNormal D frame first second mode internal -
      frameOscillatorNormal D frame first second mode internal * matterAux D frame inverse xAxis yAxis =
      ((axisAuxDegree D xAxis yAxis first : ℂ) + (axisAuxDegree D xAxis yAxis second : ℂ)) •
        frameOscillatorNormal D frame first second mode internal := by
  by_cases omitted : internal = 0 ∨ internal = mode
  · simp [frameOscillatorNormal, omitted]
  have firstNonzero : internal ≠ 0 := fun zero => omitted (Or.inl zero)
  have secondNonzero : mode - internal ≠ 0 := by intro zero; apply omitted; right; omega
  have firstGrade := matterAux_current D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual first internal firstNonzero
  have secondGrade := matterAux_current D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual second (mode - internal) secondNonzero
  by_cases negative : internal < 0
  · simp only [frameOscillatorNormal, if_neg omitted, if_pos negative]
    calc
      _ = (matterAux D frame inverse xAxis yAxis * directionalCurrent D (frame first) internal -
            directionalCurrent D (frame first) internal * matterAux D frame inverse xAxis yAxis) *
            directionalCurrent D (frame second) (mode - internal) +
          directionalCurrent D (frame first) internal *
            (matterAux D frame inverse xAxis yAxis * directionalCurrent D (frame second) (mode - internal) -
             directionalCurrent D (frame second) (mode - internal) * matterAux D frame inverse xAxis yAxis) := by
        noncomm_ring
      _ = _ := by rw [firstGrade, secondGrade]; simp [smul_mul_assoc, mul_smul_comm, add_smul]
  · simp only [frameOscillatorNormal, if_neg omitted, if_neg negative]
    calc
      _ = (matterAux D frame inverse xAxis yAxis * directionalCurrent D (frame second) (mode - internal) -
            directionalCurrent D (frame second) (mode - internal) * matterAux D frame inverse xAxis yAxis) *
            directionalCurrent D (frame first) internal +
          directionalCurrent D (frame second) (mode - internal) *
            (matterAux D frame inverse xAxis yAxis * directionalCurrent D (frame first) internal -
             directionalCurrent D (frame first) internal * matterAux D frame inverse xAxis yAxis) := by
        noncomm_ring
      _ = _ := by rw [secondGrade, firstGrade]; simp [smul_mul_assoc, mul_smul_comm, add_smul, add_comm]

theorem weighted_frameOscillatorNormal_commutes (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (first second : Fin D.rank) (mode internal : ℤ) :
    matterAux D frame inverse xAxis yAxis *
        (frameH D H inverse first second • frameOscillatorNormal D frame first second mode internal) -
      (frameH D H inverse first second • frameOscillatorNormal D frame first second mode internal) *
        matterAux D frame inverse xAxis yAxis = 0 := by
  have balance := frameH_aux_balance D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse xAxis yAxis distinct xDual yDual first second
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
    matterAux_frameOscillatorNormal D frame inverse leftFrameInverse rightFrameInverse
      xAxis yAxis distinct xDual yDual, smul_smul, mul_comm, balance, zero_smul]

theorem matterAux_oscillatorSugawara_commutator (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (mode : ℤ) :
    matterAux D frame inverse xAxis yAxis * oscillatorSugawaraMode D H mode -
      oscillatorSugawaraMode D H mode * matterAux D frame inverse xAxis yAxis = 0 := by
  classical
  apply LinearMap.ext
  intro matter
  change matterAux D frame inverse xAxis yAxis (oscillatorSugawaraMode D H mode matter) -
    oscillatorSugawaraMode D H mode (matterAux D frame inverse xAxis yAxis matter) = 0
  apply sub_eq_zero.mpr
  rw [oscillatorSugawaraMode_covariance D H frame inverse leftFrameInverse rightFrameInverse,
    oscillatorSugawaraMode_covariance D H frame inverse leftFrameInverse rightFrameInverse]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro axes axesMember
  have weightedFinite (input : Carrier D) :=
    (frameOscillatorNormal_finite D frame axes.1 axes.2 mode input).fun_comp
      (show frameH D H inverse axes.1 axes.2 • (0 : Carrier D) = 0 by simp)
  have termCommute (internal : ℤ) := congrArg
    (fun operator : Module.End ℂ (Carrier D) => operator matter)
    (weighted_frameOscillatorNormal_commutes D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse xAxis yAxis distinct xDual yDual axes.1 axes.2 mode internal)
  have mapped := (matterAux D frame inverse xAxis yAxis).toAddMonoidHom.map_finsum (weightedFinite matter)
  simp only [LinearMap.toAddMonoidHom_coe] at mapped
  rw [← map_smul, smul_finsum' _ (frameOscillatorNormal_finite D frame axes.1 axes.2 mode matter), mapped,
    smul_finsum' _ (frameOscillatorNormal_finite D frame axes.1 axes.2 mode
      (matterAux D frame inverse xAxis yAxis matter))]
  apply finsum_congr
  intro internal
  exact sub_eq_zero.mp (by
    simpa only [LinearMap.sub_apply, LinearMap.zero_apply, Module.End.mul_apply,
      LinearMap.smul_apply, map_smul] using termCommute internal)

theorem auxiliary_commutator_split (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (operator : Module.End ℂ (State D)) :
    auxiliary D frame inverse xAxis yAxis * operator - operator * auxiliary D frame inverse xAxis yAxis =
      (matterAuxLift D frame inverse xAxis yAxis * operator - operator * matterAuxLift D frame inverse xAxis yAxis) +
      (LatticeBcGhostBrstGhostNumber.J D * operator - operator * LatticeBcGhostBrstGhostNumber.J D) := by
  unfold auxiliary
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one]
  abel

theorem auxiliary_oscillator_commutator (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (mode : ℤ) :
    auxiliary D frame inverse xAxis yAxis * oscillatorLift D H mode -
      oscillatorLift D H mode * auxiliary D frame inverse xAxis yAxis = 0 := by
  have lifted := congrArg (LinearMap.rTensorHom (Fock ℂ))
    (matterAux_oscillatorSugawara_commutator D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse xAxis yAxis distinct xDual yDual mode)
  simp only [map_sub, map_zero, LinearMap.coe_rTensorHom, LinearMap.rTensor_mul] at lifted
  have ghostCommute : LatticeBcGhostBrstGhostNumber.J D * oscillatorLift D H mode =
      oscillatorLift D H mode * LatticeBcGhostBrstGhostNumber.J D := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [oscillatorLift, LatticeBcGhostBrstGhostNumber.J, Module.End.mul_apply]
  rw [auxiliary_commutator_split, ghostCommute, sub_self, add_zero]
  simpa only [matterAuxLift, oscillatorLift, LinearMap.rTensor_def] using lifted

theorem matterAux_sugawara_zero_commutator (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) :
    matterAux D frame inverse xAxis yAxis * sugawaraMode D H 0 -
      sugawaraMode D H 0 * matterAux D frame inverse xAxis yAxis = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro charge polynomial
  obtain ⟨coordinates, coordinateEquality⟩ :=
    (coordinateSub_bijective D frame inverse leftFrameInverse rightFrameInverse).2 polynomial
  subst polynomial
  change matterAux D frame inverse xAxis yAxis
      (sugawaraMode D H 0 (Finsupp.single charge (coordinateSub D frame coordinates))) -
    sugawaraMode D H 0 (matterAux D frame inverse xAxis yAxis
      (Finsupp.single charge (coordinateSub D frame coordinates))) = 0
  induction coordinates using MvPolynomial.induction_on' with
  | monomial powers scalar =>
      have energy := sugawaraMode_weighted_homogeneous D H leftGramInverse rightGramInverse charge
        (coordinateSub D frame (MvPolynomial.monomial powers scalar))
        (Finsupp.weight (frequencyWeight D) powers) (coordinateSub_monomial_frequency D frame powers scalar)
      have degree : matterAux D frame inverse xAxis yAxis
          (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))) =
          (Finsupp.weight (auxiliaryWeight D xAxis yAxis) powers : ℂ) •
            Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) := by
        simp only [matterAux_single, polynomialAux_coordinateSub D frame inverse rightFrameInverse,
          auxDiagonal_monomial, map_smul, Finsupp.smul_single]
      rw [energy, map_smul, degree, map_smul, energy]
      simp [smul_smul, mul_comm]
  | add first second firstProof secondProof =>
      simpa only [map_add, Finsupp.single_add, add_sub_add_comm, firstProof, secondProof, zero_add]

theorem auxiliary_M_zero_commutator (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) :
    auxiliary D frame inverse xAxis yAxis * M D H 0 - M D H 0 * auxiliary D frame inverse xAxis yAxis = 0 := by
  have lifted := congrArg (LinearMap.rTensorHom (Fock ℂ))
    (matterAux_sugawara_zero_commutator D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse xAxis yAxis)
  simp only [map_sub, map_zero, LinearMap.coe_rTensorHom, LinearMap.rTensor_mul] at lifted
  have ghostCommute : LatticeBcGhostBrstGhostNumber.J D * M D H 0 =
      M D H 0 * LatticeBcGhostBrstGhostNumber.J D := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [M, LatticeBcGhostBrstGhostNumber.J, Module.End.mul_apply]
  rw [auxiliary_commutator_split, ghostCommute, sub_self, add_zero]
  simpa only [matterAuxLift, M, LinearMap.rTensor_def] using lifted

theorem auxiliary_C_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) (mode : ℤ) :
    auxiliary D frame inverse xAxis yAxis * C D mode - C D mode * auxiliary D frame inverse xAxis yAxis = C D mode := by
  have ghostGrade := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostNumber.J_c_commutator (K := ℂ) mode)
  simp only [map_sub, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at ghostGrade
  have matterCommute : matterAuxLift D frame inverse xAxis yAxis * C D mode =
      C D mode * matterAuxLift D frame inverse xAxis yAxis := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [matterAuxLift, C, Module.End.mul_apply]
  rw [auxiliary_commutator_split, matterCommute, sub_self, zero_add]
  simpa only [LatticeBcGhostBrstGhostNumber.J, C, LinearMap.lTensor_def] using ghostGrade

theorem auxiliary_B_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) (mode : ℤ) :
    auxiliary D frame inverse xAxis yAxis * B D mode - B D mode * auxiliary D frame inverse xAxis yAxis = -B D mode := by
  have ghostGrade := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostNumber.J_b_commutator (K := ℂ) mode)
  simp only [map_sub, map_neg, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at ghostGrade
  have matterCommute : matterAuxLift D frame inverse xAxis yAxis * B D mode =
      B D mode * matterAuxLift D frame inverse xAxis yAxis := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [matterAuxLift, B, Module.End.mul_apply]
  rw [auxiliary_commutator_split, matterCommute, sub_self, zero_add]
  simpa only [LatticeBcGhostBrstGhostNumber.J, B, LinearMap.lTensor_def] using ghostGrade

theorem auxiliary_G_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) (mode : ℤ) :
    auxiliary D frame inverse xAxis yAxis * G D mode - G D mode * auxiliary D frame inverse xAxis yAxis = 0 := by
  have ghostGrade := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostNumber.J_L_commutator (K := ℂ) mode)
  simp only [map_sub, map_zero, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at ghostGrade
  have matterCommute : matterAuxLift D frame inverse xAxis yAxis * G D mode =
      G D mode * matterAuxLift D frame inverse xAxis yAxis := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [matterAuxLift, G, Module.End.mul_apply]
  rw [auxiliary_commutator_split, matterCommute, sub_self, zero_add]
  simpa only [LatticeBcGhostBrstGhostNumber.J, G, LinearMap.lTensor_def] using ghostGrade

theorem auxiliary_N_commutator (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) (mode : ℤ) :
    auxiliary D frame inverse xAxis yAxis * N D mode - N D mode * auxiliary D frame inverse xAxis yAxis = N D mode := by
  have cGrade := auxiliary_C_commutator D frame inverse xAxis yAxis (-mode)
  have gGrade := auxiliary_G_commutator D frame inverse xAxis yAxis mode
  by_cases branch : -1 ≤ mode
  · simp only [N, if_pos branch, ← Module.End.mul_eq_comp]
    calc
      _ = (auxiliary D frame inverse xAxis yAxis * C D (-mode) - C D (-mode) *
            auxiliary D frame inverse xAxis yAxis) * G D mode + C D (-mode) *
          (auxiliary D frame inverse xAxis yAxis * G D mode - G D mode *
            auxiliary D frame inverse xAxis yAxis) := by
        simp only [sub_mul, mul_sub, add_mul, mul_add]
        noncomm_ring
      _ = _ := by rw [cGrade, gGrade]; simp
  · simp only [N, if_neg branch, ← Module.End.mul_eq_comp]
    calc
      _ = (auxiliary D frame inverse xAxis yAxis * G D mode - G D mode *
            auxiliary D frame inverse xAxis yAxis) * C D (-mode) + G D mode *
          (auxiliary D frame inverse xAxis yAxis * C D (-mode) - C D (-mode) *
            auxiliary D frame inverse xAxis yAxis) := by
        simp only [sub_mul, mul_sub, add_mul, mul_add]
        noncomm_ring
      _ = _ := by rw [gGrade, cGrade]; simp

theorem auxiliary_A_zero_commutator (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) :
    auxiliary D frame inverse xAxis yAxis * A D H 0 - A D H 0 * auxiliary D frame inverse xAxis yAxis = A D H 0 := by
  have cGrade := auxiliary_C_commutator D frame inverse xAxis yAxis 0
  have mGrade := auxiliary_M_zero_commutator D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse xAxis yAxis
  have nGrade := auxiliary_N_commutator D frame inverse xAxis yAxis 0
  simp only [A, ← Module.End.mul_eq_comp, neg_zero]
  calc
    _ = (auxiliary D frame inverse xAxis yAxis * C D 0 - C D 0 * auxiliary D frame inverse xAxis yAxis) * M D H 0 +
        C D 0 * (auxiliary D frame inverse xAxis yAxis * M D H 0 - M D H 0 * auxiliary D frame inverse xAxis yAxis) +
        (2 : ℂ)⁻¹ • (auxiliary D frame inverse xAxis yAxis * N D 0 - N D 0 * auxiliary D frame inverse xAxis yAxis) := by
      simp only [mul_add, add_mul, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, smul_sub,
        neg_smul]
      noncomm_ring
    _ = _ := by rw [cGrade, mGrade, nGrade]; simp

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
