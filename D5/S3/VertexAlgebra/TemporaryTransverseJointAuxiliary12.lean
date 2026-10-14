import D5.S3.VertexAlgebra.TemporaryTransverseJointAuxiliary11
namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraVirasoro LatticeSugawaraConformal LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def chargeEmbedding (D : LatticeData) (charge : Charge D) :
    Oscillator D ⊗[ℂ] Fock ℂ →ₗ[ℂ] State D :=
  TensorProduct.map (Finsupp.lsingle charge) LinearMap.id

def chargeExtraction (D : LatticeData) (charge : Charge D) :
    State D →ₗ[ℂ] Oscillator D ⊗[ℂ] Fock ℂ :=
  TensorProduct.map (Finsupp.lapply charge) LinearMap.id

def chargeProjection (D : LatticeData) (charge : Charge D) : Module.End ℂ (State D) :=
  (chargeEmbedding D charge).comp (chargeExtraction D charge)

theorem chargeEmbedding_range_iff (D : LatticeData) (charge : Charge D) (state : State D) :
    state ∈ LinearMap.range (chargeEmbedding D charge) ↔ chargeProjection D charge state = state := by
  have extractEmbed : (chargeExtraction D charge).comp (chargeEmbedding D charge) = LinearMap.id := by
    apply TensorProduct.ext'
    intro polynomial ghost
    simp [chargeExtraction, chargeEmbedding, Finsupp.lsingle, Finsupp.lapply,
      TensorProduct.map_tmul, LinearMap.comp_apply]
  constructor
  · rintro ⟨input, rfl⟩
    change chargeEmbedding D charge (chargeExtraction D charge (chargeEmbedding D charge input)) = _
    have recovered := LinearMap.congr_fun extractEmbed input
    rw [show chargeExtraction D charge (chargeEmbedding D charge input) = input from recovered]
  · intro fixed
    exact ⟨chargeExtraction D charge state, fixed⟩

theorem raisingOne_aux_degree_one_sector (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D charge nullDirection ≠ 0)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (state : State D) (sector : chargeProjection D charge state = state) :
    auxiliary D frame inverse xAxis yAxis (raisingOne D H charge nullDirection state) -
      raisingOne D H charge nullDirection (auxiliary D frame inverse xAxis yAxis state) =
      raisingOne D H charge nullDirection state := by
  have onInput (input : Oscillator D ⊗[ℂ] Fock ℂ) :
      auxiliary D frame inverse xAxis yAxis (raisingOne D H charge nullDirection (chargeEmbedding D charge input)) -
        raisingOne D H charge nullDirection (auxiliary D frame inverse xAxis yAxis (chargeEmbedding D charge input)) =
        raisingOne D H charge nullDirection (chargeEmbedding D charge input) := by
    induction input using TensorProduct.induction_on with
    | zero => simp
    | tmul polynomial ghost =>
        simpa only [chargeEmbedding, TensorProduct.map_tmul, Finsupp.lsingle_apply, LinearMap.id_apply] using
          raisingOne_aux_degree_one_tmul D H frame inverse leftGramInverse rightGramInverse
            leftFrameInverse rightFrameInverse charge nullDirection null nonzero xAxis yAxis distinct xDual yDual
            polynomial ghost
    | add first second firstProof secondProof =>
        simpa only [map_add, add_sub_add_comm, firstProof, secondProof]
  obtain ⟨input, inputEquality⟩ := (chargeEmbedding_range_iff D charge state).mpr sector
  rw [← inputEquality]
  exact onInput input

theorem raisingTwo_aux_degree_two (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis) (xRow : frame xAxis = nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    auxiliary D frame inverse xAxis yAxis * raisingTwo D charge nullDirection -
      raisingTwo D charge nullDirection * auxiliary D frame inverse xAxis yAxis =
      (2 : ℂ) • raisingTwo D charge nullDirection := by
  have actual := auxiliary_dSum_commutator D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual xAxis
  have actual' : auxiliary D frame inverse xAxis yAxis * dSum D nullDirection -
      dSum D nullDirection * auxiliary D frame inverse xAxis yAxis =
      (2 : ℂ) • dSum D nullDirection := by
    simpa [axisAuxDegree, xRow, one_add_one_eq_two] using actual
  have scaled := congrArg (fun operator : Module.End ℂ (State D) =>
    chosenQ D charge nullDirection • operator) actual'
  simpa only [raisingTwo, mul_smul_comm, smul_mul_assoc, smul_sub] using
    scaled.trans (smul_comm (chosenQ D charge nullDirection) (2 : ℂ) (dSum D nullDirection))

theorem original_Q_strict_auxiliary_split (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D charge nullDirection ≠ 0)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xRow : frame xAxis = nullDirection) (yRow : frame yAxis = adaptedPartner D charge nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (degree : ℤ) (state : State D) (sector : chargeProjection D charge state = state)
    (homogeneous : AuxHomogeneous D frame inverse xAxis yAxis degree state) :
    (Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection)) state =
        raisingOne D H charge nullDirection state + raisingTwo D charge nullDirection state ∧
      AuxHomogeneous D frame inverse xAxis yAxis (degree + 1) (raisingOne D H charge nullDirection state) ∧
      AuxHomogeneous D frame inverse xAxis yAxis (degree + 2) (raisingTwo D charge nullDirection state) ∧
      auxiliary D frame inverse xAxis yAxis *
          delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection) -
        delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection) *
          auxiliary D frame inverse xAxis yAxis = 0 ∧
      auxiliary D frame inverse xAxis yAxis * R D nullDirection (chosenP D charge nullDirection) -
        R D nullDirection (chosenP D charge nullDirection) * auxiliary D frame inverse xAxis yAxis = 0 := by
  have oneGrade := raisingOne_aux_degree_one_sector D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse charge nullDirection null nonzero xAxis yAxis distinct xDual yDual state sector
  have twoGrade := congrArg (fun operator : Module.End ℂ (State D) => operator state)
    (raisingTwo_aux_degree_two D frame inverse leftFrameInverse rightFrameInverse charge nullDirection
      xAxis yAxis distinct xRow xDual yDual)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at twoGrade
  have deltaGrade := auxiliary_delta_zero D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual (chosenP D charge nullDirection)
  have rGrade := auxiliary_R_zero D frame inverse leftFrameInverse rightFrameInverse
    xAxis yAxis distinct xDual yDual (chosenP D charge nullDirection)
  rw [yRow] at deltaGrade
  rw [xRow] at rGrade
  refine ⟨?_, ?_, ?_, deltaGrade, rGrade⟩
  · simp only [raisingOne, raisingTwo, LinearMap.sub_apply, LinearMap.smul_apply]
    abel
  · unfold AuxHomogeneous at homogeneous ⊢
    have equality := sub_eq_iff_eq_add.mp oneGrade
    rw [homogeneous, map_smul] at equality
    simpa only [Int.cast_add, Int.cast_one, add_smul, one_smul, add_comm] using equality
  · unfold AuxHomogeneous at homogeneous ⊢
    have equality := sub_eq_iff_eq_add.mp twoGrade
    rw [homogeneous, map_smul] at equality
    simpa only [Int.cast_add, Int.cast_ofNat, add_smul, add_comm] using equality

theorem original_Q_corrected_xy_finsum (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D charge nullDirection ≠ 0)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (polynomial : Oscillator D) (ghost : Fock ℂ) :
    (Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection))
        (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) =
      ∑ᶠ mode : ℤ, if mode = 0 then A D H 0 (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) else
        chosenQ D charge nullDirection • C D (-mode)
          (O D nullDirection mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) +
        C D (-mode) (((2 : ℂ)⁻¹ •
          ((∑ᶠ internal : ℤ, frameOscillatorNormal D frame xAxis yAxis mode internal (Finsupp.single charge polynomial)) +
           (∑ᶠ internal : ℤ, frameOscillatorNormal D frame yAxis xAxis mode internal (Finsupp.single charge polynomial)) +
           ∑ first ∈ transverseAxes D xAxis yAxis, ∑ second ∈ transverseAxes D xAxis yAxis,
             frameH D H inverse first second • ∑ᶠ internal : ℤ,
               frameOscillatorNormal D frame first second mode internal (Finsupp.single charge polynomial))) ⊗ₜ[ℂ] ghost) +
        (2 : ℂ)⁻¹ • N D mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) := by
  rw [original_Q_corrected_finsum D H leftGramInverse rightGramInverse charge nullDirection null nonzero]
  apply finsum_congr
  intro mode
  by_cases zeroMode : mode = 0
  · simp only [if_pos zeroMode]
  · simp only [if_neg zeroMode]
    rw [oscillatorSugawaraMode_xy_transverse D H frame inverse leftGramInverse rightGramInverse
      leftFrameInverse rightFrameInverse xAxis yAxis distinct xDual yDual]

theorem original_Q_coordinate_polarized_strict_energy (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0) (nonzero : chosenP D charge nullDirection ≠ 0)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xRow : frame xAxis = nullDirection) (yRow : frame yAxis = adaptedPartner D charge nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) :
    let state := Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ]
      downWord subset down
    let degree := (axisExponentCount D xAxis powers : ℤ) - (axisExponentCount D yAxis powers : ℤ) +
      epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ)
    (Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection)) state =
        raisingOne D H charge nullDirection state + raisingTwo D charge nullDirection state ∧
      AuxHomogeneous D frame inverse xAxis yAxis (degree + 1) (raisingOne D H charge nullDirection state) ∧
      AuxHomogeneous D frame inverse xAxis yAxis (degree + 2) (raisingTwo D charge nullDirection state) ∧
      (M D H 0 + G D 0) state =
        (chosenH D charge + (Finsupp.weight (frequencyWeight D) powers : ℂ) +
          (polarizedLevel subset : ℂ) - 1) • state := by
  dsimp only
  let state := Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar)) ⊗ₜ[ℂ]
    downWord subset down
  have sector : chargeProjection D charge state = state := by
    apply (chargeEmbedding_range_iff D charge state).mp
    refine ⟨coordinateSub D frame (MvPolynomial.monomial powers scalar) ⊗ₜ[ℂ] downWord subset down, ?_⟩
    simp only [chargeEmbedding, TensorProduct.map_tmul, Finsupp.lsingle_apply, LinearMap.id_apply, state]
  have homogeneous := original_coordinate_polarized_aux_degree D frame inverse rightFrameInverse
    xAxis yAxis charge powers scalar subset
  rw [signed_weight_axis_counts D xAxis yAxis distinct] at homogeneous
  have strict := original_Q_strict_auxiliary_split D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse charge nullDirection null nonzero xAxis yAxis distinct xRow yRow xDual yDual
    _ state sector homogeneous
  exact ⟨strict.1, strict.2.1, strict.2.2.1,
    original_total_energy_coordinate_polarized D H frame leftGramInverse rightGramInverse charge powers scalar subset⟩

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
