import D5.S3.VertexAlgebra.TemporaryOriginalQuartet05

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def etaSite (frequency : ℕ) : ℕ := if frequency = 0 then 1 else 2 * (frequency - 1)

def thetaSite (frequency : ℕ) : ℕ := 2 * frequency + 5

def ghostBlock (frequency : ℕ) : Module.End ℂ (Fock ℂ) :=
  c (-((frequency : ℤ) + 1)) * b ((frequency : ℤ) + 1) +
    b (-((frequency : ℤ) + 1)) * c ((frequency : ℤ) + 1)

theorem sign_erase_self (site : ℕ) (subset : Finset ℕ) :
    sign (K := ℂ) site (subset.erase site) = sign site subset := by
  have sameFilter : (subset.erase site).filter (fun other => other < site) =
      subset.filter (fun other => other < site) := by
    ext other
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · tauto
    · intro member
      exact ⟨⟨ne_of_lt member.2, member.1⟩, member.2⟩
  simp only [sign, sameFilter]

theorem sign_square (site : ℕ) (subset : Finset ℕ) :
    sign (K := ℂ) site subset * sign site subset = 1 := by
  simp [sign, ← mul_pow]

theorem original_site_number (site : ℕ) (subset : Finset ℕ) :
    create (K := ℂ) site (annihilate site (Finsupp.single subset 1)) =
      if site ∈ subset then Finsupp.single subset 1 else 0 := by
  by_cases present : site ∈ subset
  · simp [create, annihilate, createBasis, annihilateBasis, present,
      sign_erase_self, Finset.insert_erase present, Finsupp.smul_single,
      smul_smul, sign_square]
  · simp [create, annihilate, annihilateBasis, present]

theorem original_site_hole_number (site : ℕ) (subset : Finset ℕ) :
    annihilate (K := ℂ) site (create site (Finsupp.single subset 1)) =
      if site ∈ subset then 0 else Finsupp.single subset 1 := by
  by_cases present : site ∈ subset
  · simp [create, createBasis, present]
  · have unchangedSign : sign (K := ℂ) site (insert site subset) = sign site subset := by
      simp [sign, Finset.filter_insert]
    simp [create, annihilate, createBasis, annihilateBasis, present,
      unchangedSign, Finsupp.smul_single, smul_smul, sign_square]

theorem ghostBlock_original_basis (frequency : ℕ) (subset : Finset ℕ) :
    ghostBlock frequency (downWord subset down) =
      (((if thetaSite frequency ∈ subset then 1 else 0 : ℕ) +
        (if etaSite frequency ∈ subset then 1 else 0 : ℕ) : ℕ) : ℂ) • downWord subset down := by
  by_cases emptySubset : subset = ∅
  · subst subset
    have emptyAction := ghost_part_normalK_down ((frequency : ℤ) + 1) (by omega)
    simpa [ghostBlock, downWord] using emptyAction
  have positiveB : b (K := ℂ) ((frequency : ℤ) + 1) = annihilate (thetaSite frequency) := by
    have branch : ¬ (frequency : ℤ) + 1 ≤ -2 := by omega
    have index : 2 * ((frequency : ℤ) + 1 + 1).toNat + 1 = thetaSite frequency := by
      unfold thetaSite
      omega
    simp only [b, if_neg branch, index]
  have negativeC : c (K := ℂ) (-((frequency : ℤ) + 1)) = create (thetaSite frequency) := by
    have branch : -((frequency : ℤ) + 1) ≤ 1 := by omega
    have index : 2 * (1 - -((frequency : ℤ) + 1)).toNat + 1 = thetaSite frequency := by
      unfold thetaSite
      omega
    simp only [c, if_pos branch, index]
  have thetaDifferent : thetaSite frequency ≠ 1 := by unfold thetaSite; omega
  rw [signed_down_word]
  simp only [polarizedBasis, map_smul]
  by_cases lowest : frequency = 0
  · subst frequency
    have negativeB : b (K := ℂ) (-(((0 : ℕ) : ℤ) + 1)) = annihilate 1 := by simp [b]
    have positiveC : c (K := ℂ) (((0 : ℕ) : ℤ) + 1) = create 1 := by simp [c]
    have hole : 1 ∉ toggleOne subset ↔ 1 ∈ subset := by
      by_cases present : 1 ∈ subset <;> simp [toggleOne, present]
    have lowMembership : 1 ∈ toggleOne subset ↔ 1 ∉ subset := by
      by_cases present : 1 ∈ subset <;> simp [toggleOne, present]
    rw [ghostBlock, negativeC, positiveB, negativeB, positiveC]
    simp only [LinearMap.add_apply, Module.End.mul_apply,
      original_site_number, original_site_hole_number]
    by_cases thetaPresent : thetaSite 0 ∈ subset <;> by_cases etaPresent : 1 ∈ subset <;>
      simp only [toggleOne_mem _ _ thetaDifferent, hole, lowMembership,
        etaSite, thetaPresent, etaPresent, eq_self_iff_true, if_true, if_false,
        not_true_eq_false, not_false_eq_true, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
        zero_smul, smul_zero, zero_add, add_zero, one_smul] <;> module
  · have negativeB : b (K := ℂ) (-((frequency : ℤ) + 1)) = create (etaSite frequency) := by
      have branch : -((frequency : ℤ) + 1) ≤ -2 := by omega
      have index : 2 * (-(-((frequency : ℤ) + 1)) - 2).toNat = etaSite frequency := by
        simp only [etaSite, if_neg lowest]
        omega
      simp only [b, if_pos branch, index]
    have positiveC : c (K := ℂ) ((frequency : ℤ) + 1) = annihilate (etaSite frequency) := by
      have branch : ¬ (frequency : ℤ) + 1 ≤ 1 := by omega
      have index : 2 * ((frequency : ℤ) + 1 - 2).toNat = etaSite frequency := by
        simp only [etaSite, if_neg lowest]
        omega
      simp only [c, if_neg branch, index]
    have etaDifferent : etaSite frequency ≠ 1 := by simp only [etaSite, if_neg lowest]; omega
    rw [ghostBlock, negativeC, positiveB, negativeB, positiveC]
    simp only [LinearMap.add_apply, Module.End.mul_apply, original_site_number]
    by_cases thetaPresent : thetaSite frequency ∈ subset <;>
      by_cases etaPresent : etaSite frequency ∈ subset <;>
      simp only [toggleOne_mem _ _ thetaDifferent, toggleOne_mem _ _ etaDifferent,
        thetaPresent, etaPresent, if_true, if_false, Nat.cast_add, Nat.cast_zero,
        Nat.cast_one, zero_smul, smul_zero, zero_add, add_zero, one_smul] <;> module

theorem coordinateDerivative_axis (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (direction : Fin D.rank → ℂ)
    (axis : Fin D.rank) (frequency : ℕ)
    (dual : ∀ row, gramPair D direction (frame row) = if row = axis then 1 else 0) :
    coordinateDerivative D frame direction frequency =
      (MvPolynomial.pderiv (axis, frequency)).toLinearMap := by
  classical
  simp [coordinateDerivative, dual]

theorem original_bosonic_mode_number (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (creatorRow annihilatorRow : Fin D.rank)
    (dual : ∀ row, gramPair D (frame annihilatorRow) (frame row) =
      if row = creatorRow then 1 else 0)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (frequency : ℕ) :
    directionalPolynomialCurrent D (frame creatorRow) charge (-((frequency : ℤ) + 1))
      (directionalPolynomialCurrent D (frame annihilatorRow) charge ((frequency : ℤ) + 1)
        (coordinateSub D frame (MvPolynomial.monomial powers scalar))) =
      (frequency + 1 : ℂ) • (powers (creatorRow, frequency) : ℂ) •
        coordinateSub D frame (MvPolynomial.monomial powers scalar) := by
  rw [directionalPolynomialCurrent_positive, coordinateDerivative_axis D frame
    (frame annihilatorRow) creatorRow frequency dual, map_smul]
  rw [show -((frequency : ℤ) + 1) = -(frequency : ℤ) - 1 by omega]
  change (frequency + 1 : ℂ) • directionalPolynomialCurrent D (frame creatorRow) charge
    (-(frequency : ℤ) - 1)
    (coordinateSub D frame (MvPolynomial.pderiv (creatorRow, frequency)
      (MvPolynomial.monomial powers scalar))) = _
  rw [directionalPolynomialCurrent_negative, MvPolynomial.X_mul_pderiv_monomial, map_nsmul]
  simp only [Nat.cast_smul_eq_nsmul]

theorem original_K_block_count (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ)
    (subset : Finset ℕ) (frequency : ℕ) :
    let state := Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))
      ⊗ₜ[ℂ] downWord subset down
    normalKAtom D (frame xAxis) (frame yAxis) ((frequency : ℤ) + 1) state +
      normalKAtom D (frame xAxis) (frame yAxis) (-((frequency : ℤ) + 1)) state =
      (((powers (xAxis, frequency) + powers (yAxis, frequency) +
        (if thetaSite frequency ∈ subset then 1 else 0) +
        (if etaSite frequency ∈ subset then 1 else 0) : ℕ) : ℂ)) • state := by
  let matter := Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))
  let ghost := downWord subset down
  have positive : 0 < (frequency : ℤ) + 1 := by omega
  have nonzeroMode : (frequency : ℤ) + 1 ≠ 0 := by omega
  have negativeNonzero : -((frequency : ℤ) + 1) ≠ 0 := by omega
  have negative : ¬ 0 < -((frequency : ℤ) + 1) := by omega
  have absPositive : ((frequency : ℤ) + 1).natAbs = frequency + 1 := by omega
  have absNegative : (-((frequency : ℤ) + 1)).natAbs = frequency + 1 := by omega
  have scalarNonzero : (frequency + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : frequency + 1 ≠ 0)
  have scalarCancel (count : ℂ) : (frequency + 1 : ℂ)⁻¹ * ((frequency + 1 : ℂ) * count) = count := by
    rw [← mul_assoc, inv_mul_cancel₀ scalarNonzero, one_mul]
  have xNumber := original_bosonic_mode_number D frame xAxis yAxis xDual charge powers scalar frequency
  have yNumber := original_bosonic_mode_number D frame yAxis xAxis yDual charge powers scalar frequency
  have matterNumber :
      ((frequency + 1 : ℂ)⁻¹) •
        ((O D (frame xAxis) (-((frequency : ℤ) + 1)) * O D (frame yAxis) ((frequency : ℤ) + 1))
          (matter ⊗ₜ[ℂ] ghost) +
        (O D (frame yAxis) (-((frequency : ℤ) + 1)) * O D (frame xAxis) ((frequency : ℤ) + 1))
          (matter ⊗ₜ[ℂ] ghost)) =
      ((powers (xAxis, frequency) + powers (yAxis, frequency) : ℕ) : ℂ) •
        (matter ⊗ₜ[ℂ] ghost) := by
    simp only [O, Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      matter, directionalCurrent_single, xNumber, yNumber, ← Finsupp.smul_single,
      ← TensorProduct.smul_tmul', smul_add, smul_smul, scalarCancel,
      Nat.cast_add, Nat.cast_one, add_smul]
  have ghostNumber :
      ((C D (-((frequency : ℤ) + 1)) * B D ((frequency : ℤ) + 1)) (matter ⊗ₜ[ℂ] ghost) +
        (B D (-((frequency : ℤ) + 1)) * C D ((frequency : ℤ) + 1)) (matter ⊗ₜ[ℂ] ghost)) =
      (((if thetaSite frequency ∈ subset then 1 else 0 : ℕ) +
        (if etaSite frequency ∈ subset then 1 else 0 : ℕ) : ℕ) : ℂ) • (matter ⊗ₜ[ℂ] ghost) := by
    have actual := ghostBlock_original_basis frequency subset
    simpa only [C, B, Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      ← TensorProduct.tmul_add, ghostBlock, LinearMap.add_apply, TensorProduct.tmul_smul, ghost]
      using congrArg (fun state : Fock ℂ => matter ⊗ₜ[ℂ] state) actual
  change normalKAtom D (frame xAxis) (frame yAxis) ((frequency : ℤ) + 1) (matter ⊗ₜ[ℂ] ghost) +
    normalKAtom D (frame xAxis) (frame yAxis) (-((frequency : ℤ) + 1)) (matter ⊗ₜ[ℂ] ghost) = _
  simp only [normalKAtom, if_neg nonzeroMode, if_neg negativeNonzero, if_pos positive,
    if_neg negative, neg_neg, absPositive, absNegative, LinearMap.add_apply,
    LinearMap.smul_apply, Nat.cast_add, Nat.cast_one]
  calc
    _ = ((frequency + 1 : ℂ)⁻¹) •
          ((O D (frame xAxis) (-((frequency : ℤ) + 1)) * O D (frame yAxis) ((frequency : ℤ) + 1))
            (matter ⊗ₜ[ℂ] ghost) +
          (O D (frame yAxis) (-((frequency : ℤ) + 1)) * O D (frame xAxis) ((frequency : ℤ) + 1))
            (matter ⊗ₜ[ℂ] ghost)) +
          ((C D (-((frequency : ℤ) + 1)) * B D ((frequency : ℤ) + 1)) (matter ⊗ₜ[ℂ] ghost) +
          (B D (-((frequency : ℤ) + 1)) * C D ((frequency : ℤ) + 1)) (matter ⊗ₜ[ℂ] ghost)) := by module
    _ = _ := by rw [matterNumber, ghostNumber]; push_cast; module

theorem original_Q_polarized_coordinate_consumer (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0)
    (nonzero : chosenP D charge nullDirection ≠ 0)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (xRow : frame xAxis = nullDirection)
    (yRow : frame yAxis = adaptedPartner D charge nullDirection)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) (frequency : ℕ) :
    let polynomial := coordinateSub D frame (MvPolynomial.monomial powers scalar)
    let state := Finsupp.single charge polynomial ⊗ₜ[ℂ] downWord subset down
    Function.Bijective (coordinateSub D frame) ∧
    chosenH D charge = LatticeSugawaraVirasoro.chargeQuadratic D H charge ∧
    downWord subset down = polarizationSign subset • Finsupp.single (toggleOne subset) 1 ∧
    LatticeBcGhostBrstGhostNumber.J D state =
      ((1 + epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) : ℤ) : ℂ) • state ∧
    G D 0 state = ((-1 + polarizedLevel subset : ℤ) : ℂ) • state ∧
    normalKAtom D nullDirection (adaptedPartner D charge nullDirection) ((frequency : ℤ) + 1) state +
      normalKAtom D nullDirection (adaptedPartner D charge nullDirection) (-((frequency : ℤ) + 1)) state =
      (((powers (xAxis, frequency) + powers (yAxis, frequency) +
        (if thetaSite frequency ∈ subset then 1 else 0) +
        (if etaSite frequency ∈ subset then 1 else 0) : ℕ) : ℂ)) • state ∧
    (Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection)) state =
      (∑ᶠ mode : ℤ, if mode = 0 then A D H 0 state else
        chosenQ D charge nullDirection • C D (-mode) (O D nullDirection mode state) +
        C D (-mode) (oscillatorSugawaraMode D H mode (Finsupp.single charge polynomial) ⊗ₜ[ℂ]
          downWord subset down) + (2 : ℂ)⁻¹ • N D mode state) ∧
    delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection) *
      delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection) = 0 ∧
    R D nullDirection (chosenP D charge nullDirection) * R D nullDirection (chosenP D charge nullDirection) = 0 ∧
    delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection) *
        R D nullDirection (chosenP D charge nullDirection) +
      R D nullDirection (chosenP D charge nullDirection) *
        delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection) =
      K D nullDirection (adaptedPartner D charge nullDirection)
        (adaptedPartner_relations D charge nullDirection null nonzero).1 ∧
    (∀ originalState : State D,
      K D nullDirection (adaptedPartner D charge nullDirection)
        (adaptedPartner_relations D charge nullDirection null nonzero).1 originalState =
        ∑ᶠ mode : ℤ, normalKAtom D nullDirection (adaptedPartner D charge nullDirection) mode originalState) ∧
    LatticeBcGhostBrstGhostNumber.J D *
        (Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection)) -
      (Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection)) *
        LatticeBcGhostBrstGhostNumber.J D =
      Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection) := by
  dsimp only
  have sector := original_polarized_state_sector D
    (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))) subset
  have quartet := original_chosen_quartet_algebra D H charge nullDirection null nonzero
  refine ⟨coordinateSub_bijective D frame inverse leftFrameInverse rightFrameInverse,
    chosenH_original_chargeQuadratic D H leftGramInverse rightGramInverse charge,
    signed_down_word subset, sector.1, sector.2.1, ?_, ?_,
    quartet.1, quartet.2.1, quartet.2.2.1, quartet.2.2.2.1, quartet.2.2.2.2⟩
  · simpa only [xRow, yRow] using original_K_block_count D frame xAxis yAxis xDual yDual
      charge powers scalar subset frequency
  · exact original_Q_corrected_finsum D H leftGramInverse rightGramInverse charge nullDirection
      null nonzero (coordinateSub D frame (MvPolynomial.monomial powers scalar)) (downWord subset down)

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
