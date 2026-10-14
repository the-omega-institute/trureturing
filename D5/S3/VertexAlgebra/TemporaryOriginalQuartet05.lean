import D5.S3.VertexAlgebra.TemporaryOriginalQuartet04

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def complexCharge (D : LatticeData) (charge : Charge D) : Fin D.rank → ℂ :=
  fun index => (charge index : ℂ)

def chosenP (D : LatticeData) (charge : Charge D) (nullDirection : Fin D.rank → ℂ) : ℂ :=
  gramPair D nullDirection (complexCharge D charge)

def chosenH (D : LatticeData) (charge : Charge D) : ℂ :=
  (2 : ℂ)⁻¹ * gramPair D (complexCharge D charge) (complexCharge D charge)

def chosenQ (D : LatticeData) (charge : Charge D) (nullDirection : Fin D.rank → ℂ) : ℂ :=
  chosenH D charge * (chosenP D charge nullDirection)⁻¹

def adaptedPartner (D : LatticeData) (charge : Charge D)
    (nullDirection : Fin D.rank → ℂ) : Fin D.rank → ℂ :=
  (chosenP D charge nullDirection)⁻¹ • complexCharge D charge -
    (chosenH D charge * ((chosenP D charge nullDirection)⁻¹)^2) • nullDirection

theorem gramPair_smul_left (D : LatticeData) (scalar : ℂ) (left right : Fin D.rank → ℂ) :
    gramPair D (scalar • left) right = scalar * gramPair D left right := by
  classical
  simp only [gramPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first firstMember
  apply Finset.sum_congr rfl
  intro second secondMember
  ring

theorem gramPair_smul_right (D : LatticeData) (scalar : ℂ) (left right : Fin D.rank → ℂ) :
    gramPair D left (scalar • right) = scalar * gramPair D left right := by
  rw [gramPair_symm, gramPair_smul_left, gramPair_symm D right left]

theorem gramPair_sub_left (D : LatticeData) (first second right : Fin D.rank → ℂ) :
    gramPair D (first - second) right = gramPair D first right - gramPair D second right := by
  classical
  simp [gramPair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem gramPair_sub_right (D : LatticeData) (left first second : Fin D.rank → ℂ) :
    gramPair D left (first - second) = gramPair D left first - gramPair D left second := by
  rw [gramPair_symm, gramPair_sub_left, gramPair_symm D first left, gramPair_symm D second left]

theorem adaptedPartner_relations (D : LatticeData) (charge : Charge D)
    (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0)
    (nonzero : chosenP D charge nullDirection ≠ 0) :
    gramPair D (adaptedPartner D charge nullDirection) nullDirection = 1 ∧
    gramPair D (adaptedPartner D charge nullDirection) (adaptedPartner D charge nullDirection) = 0 ∧
    complexCharge D charge =
      chosenP D charge nullDirection • adaptedPartner D charge nullDirection +
        chosenQ D charge nullDirection • nullDirection := by
  have oppositePair : gramPair D (complexCharge D charge) nullDirection =
      chosenP D charge nullDirection := by rw [gramPair_symm]; rfl
  have directPair : gramPair D nullDirection (complexCharge D charge) =
      chosenP D charge nullDirection := rfl
  have selfPair : gramPair D (complexCharge D charge) (complexCharge D charge) =
      2 * chosenH D charge := by unfold chosenH; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [adaptedPartner, gramPair_sub_left, gramPair_smul_left,
      oppositePair, null, mul_zero, sub_zero]
    exact inv_mul_cancel₀ nonzero
  · simp only [adaptedPartner, gramPair_sub_left, gramPair_sub_right,
      gramPair_smul_left, gramPair_smul_right, oppositePair, directPair, selfPair, null]
    field_simp [nonzero]
    ring
  · ext index
    change (charge index : ℂ) = chosenP D charge nullDirection *
      ((chosenP D charge nullDirection)⁻¹ * (charge index : ℂ) -
        (chosenH D charge * ((chosenP D charge nullDirection)⁻¹)^2) * nullDirection index) +
      (chosenH D charge * (chosenP D charge nullDirection)⁻¹) * nullDirection index
    field_simp [nonzero]
    ring

theorem chosenH_original_chargeQuadratic (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (charge : Charge D) : chosenH D charge = chargeQuadratic D H charge := by
  classical
  have contraction : (∑ first, ∑ second,
      H first second * chargeScalar D charge first * chargeScalar D charge second) =
      gramPair D (complexCharge D charge) (complexCharge D charge) := by
    calc
      _ = ∑ first, chargeScalar D charge first *
          (∑ second, H first second * chargeScalar D charge second) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro first firstMember
        apply Finset.sum_congr rfl
        intro second secondMember
        ring
      _ = ∑ first, chargeScalar D charge first * (charge first : ℂ) := by
        have inverseContraction (index : Fin D.rank) :=
          (inverseGram_charge_contractions D H leftInverse rightInverse charge index).2
        simp_rw [inverseContraction]
      _ = _ := by
        simp only [chargeScalar_expansion, gramPair, complexCharge, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro first firstMember
        apply Finset.sum_congr rfl
        intro second secondMember
        ring
  simp only [chosenH, chargeQuadratic, contraction]

theorem O_direction_combination (D : LatticeData) (left right : Fin D.rank → ℂ)
    (leftScalar rightScalar : ℂ) (mode : ℤ) :
    O D (leftScalar • left + rightScalar • right) mode =
      leftScalar • O D left mode + rightScalar • O D right mode := by
  classical
  have matterCombination : directionalCurrent D (leftScalar • left + rightScalar • right) mode =
      leftScalar • directionalCurrent D left mode + rightScalar • directionalCurrent D right mode := by
    simp [directionalCurrent, Pi.add_apply, Pi.smul_apply, add_smul, smul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
  apply TensorProduct.ext'
  intro matter ghost
  simp [O, matterCombination, TensorProduct.add_tmul, TensorProduct.smul_tmul]

theorem original_adapted_M_nonzero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0)
    (nonzero : chosenP D charge nullDirection ≠ 0)
    (polynomial : Oscillator D) (ghost : Fock ℂ) (mode : ℤ) (nonzeroMode : mode ≠ 0) :
    M D H mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) =
      chosenP D charge nullDirection •
        O D (adaptedPartner D charge nullDirection) mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) +
      chosenQ D charge nullDirection •
        O D nullDirection mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) +
      oscillatorSugawaraMode D H mode (Finsupp.single charge polynomial) ⊗ₜ[ℂ] ghost := by
  have decomposition := (adaptedPartner_relations D charge nullDirection null nonzero).2.2
  have native := original_tensor_sugawara_charged_separation D H leftInverse rightInverse
    charge polynomial ghost mode nonzeroMode
  change M D H mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) = _ at native
  change M D H mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) =
    O D (complexCharge D charge) mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) + _ at native
  rw [decomposition, O_direction_combination] at native
  simpa only [LinearMap.add_apply, LinearMap.smul_apply, add_assoc] using native

theorem original_A_leading_piece (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0)
    (nonzero : chosenP D charge nullDirection ≠ 0)
    (polynomial : Oscillator D) (ghost : Fock ℂ) (mode : ℤ) (nonzeroMode : mode ≠ 0) :
    A D H mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) -
      chosenP D charge nullDirection • dAtom D (adaptedPartner D charge nullDirection) mode
        (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) =
      chosenQ D charge nullDirection • C D (-mode)
        (O D nullDirection mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) +
      C D (-mode) (oscillatorSugawaraMode D H mode (Finsupp.single charge polynomial) ⊗ₜ[ℂ] ghost) +
      (2 : ℂ)⁻¹ • N D mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) := by
  simp only [A, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    dAtom, if_neg nonzeroMode, Module.End.mul_apply]
  rw [original_adapted_M_nonzero D H leftInverse rightInverse charge nullDirection null nonzero
    polynomial ghost mode nonzeroMode]
  simp only [map_add, map_smul]
  abel

theorem original_Q_corrected_finsum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (charge : Charge D) (nullDirection : Fin D.rank → ℂ)
    (null : gramPair D nullDirection nullDirection = 0)
    (nonzero : chosenP D charge nullDirection ≠ 0)
    (polynomial : Oscillator D) (ghost : Fock ℂ) :
    (Q D H - delta D (adaptedPartner D charge nullDirection) (chosenP D charge nullDirection))
      (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) =
      ∑ᶠ mode : ℤ, if mode = 0 then A D H 0 (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) else
        chosenQ D charge nullDirection • C D (-mode)
          (O D nullDirection mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost)) +
        C D (-mode) (oscillatorSugawaraMode D H mode (Finsupp.single charge polynomial) ⊗ₜ[ℂ] ghost) +
        (2 : ℂ)⁻¹ • N D mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) := by
  let state := Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost
  have originalFinite := A_finite D H state
  have leadingFinite := dAtom_finite D (adaptedPartner D charge nullDirection) state
  have scalarFinite := leadingFinite.fun_comp
    (show chosenP D charge nullDirection • (0 : State D) = 0 by simp)
  change (∑ᶠ mode : ℤ, A D H mode state) -
    chosenP D charge nullDirection •
      (∑ᶠ mode : ℤ, dAtom D (adaptedPartner D charge nullDirection) mode state) = _
  rw [smul_finsum' (chosenP D charge nullDirection) leadingFinite,
    ← finsum_sub_distrib originalFinite scalarFinite]
  apply finsum_congr
  intro mode
  by_cases zeroMode : mode = 0
  · subst mode
    simp [dAtom, state]
  · simpa only [if_neg zeroMode] using original_A_leading_piece D H leftInverse rightInverse
      charge nullDirection null nonzero polynomial ghost mode zeroMode

theorem original_chosen_quartet_algebra (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (charge : Charge D)
    (nullDirection : Fin D.rank → ℂ) (null : gramPair D nullDirection nullDirection = 0)
    (nonzero : chosenP D charge nullDirection ≠ 0) :
    let longitudinal := adaptedPartner D charge nullDirection
    let coefficient := chosenP D charge nullDirection
    let dual := (adaptedPartner_relations D charge nullDirection null nonzero).1
    delta D longitudinal coefficient * delta D longitudinal coefficient = 0 ∧
    R D nullDirection coefficient * R D nullDirection coefficient = 0 ∧
    delta D longitudinal coefficient * R D nullDirection coefficient +
      R D nullDirection coefficient * delta D longitudinal coefficient = K D nullDirection longitudinal dual ∧
    (∀ state : State D, K D nullDirection longitudinal dual state =
      ∑ᶠ mode : ℤ, normalKAtom D nullDirection longitudinal mode state) ∧
    LatticeBcGhostBrstGhostNumber.J D * (Q D H - delta D longitudinal coefficient) -
      (Q D H - delta D longitudinal coefficient) * LatticeBcGhostBrstGhostNumber.J D =
      Q D H - delta D longitudinal coefficient := by
  obtain ⟨dual, longitudinalNull, decomposition⟩ :=
    adaptedPartner_relations D charge nullDirection null nonzero
  exact original_Q_quartet_algebra D H nullDirection (adaptedPartner D charge nullDirection)
    null longitudinalNull dual (chosenP D charge nullDirection) nonzero

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
