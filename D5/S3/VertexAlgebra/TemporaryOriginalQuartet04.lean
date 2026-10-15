import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.VertexAlgebra.TemporaryOriginalQuartet03

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraVirasoro LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def oscillatorNormalSummand (D : LatticeData) (first second : Fin D.rank)
    (mode internal : ℤ) : Module.End ℂ (Carrier D) :=
  if internal = 0 ∨ internal = mode then 0 else normalSummand D first second internal (mode - internal)

theorem oscillatorNormalSummand_finite (D : LatticeData) (first second : Fin D.rank)
    (mode : ℤ) (matter : Carrier D) :
    Function.HasFiniteSupport (fun internal : ℤ =>
      oscillatorNormalSummand D first second mode internal matter) := by
  apply (normalSummand_finite D first second mode matter).subset
  intro internal nonzero
  intro originalZero
  exact nonzero (by
    by_cases omitted : internal = 0 ∨ internal = mode <;>
      simp [oscillatorNormalSummand, omitted, originalZero])

def oscillatorSugawaraMode (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (mode : ℤ) : Module.End ℂ (Carrier D) where
  toFun matter := (2 : ℂ)⁻¹ • ∑ first, ∑ second, H first second •
    ∑ᶠ internal : ℤ, oscillatorNormalSummand D first second mode internal matter
  map_add' firstMatter secondMatter := by
    have addFormula (first second : Fin D.rank) :
        (∑ᶠ internal : ℤ,
          (oscillatorNormalSummand D first second mode internal firstMatter +
            oscillatorNormalSummand D first second mode internal secondMatter)) =
        (∑ᶠ internal : ℤ, oscillatorNormalSummand D first second mode internal firstMatter) +
          (∑ᶠ internal : ℤ, oscillatorNormalSummand D first second mode internal secondMatter) :=
      finsum_add_distrib (oscillatorNormalSummand_finite D first second mode firstMatter)
        (oscillatorNormalSummand_finite D first second mode secondMatter)
    simp only [map_add]
    simp_rw [addFormula]
    simp only [smul_add, Finset.sum_add_distrib]
  map_smul' scalar matter := by
    have scalarFormula (first second : Fin D.rank) :
        (∑ᶠ internal : ℤ, scalar • oscillatorNormalSummand D first second mode internal matter) =
        scalar • (∑ᶠ internal : ℤ, oscillatorNormalSummand D first second mode internal matter) :=
      (smul_finsum' scalar (oscillatorNormalSummand_finite D first second mode matter)).symm
    simp only [map_smul, RingHom.id_apply]
    simp_rw [scalarFormula]
    simp only [Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro first firstMember
    apply Finset.sum_congr rfl
    intro second secondMember
    congr 1
    ring

theorem chargeScalar_expansion (D : LatticeData) (charge : Charge D) (index : Fin D.rank) :
    chargeScalar D charge index = ∑ coordinateIndex, (D.G index coordinateIndex : ℂ) *
      (charge coordinateIndex : ℂ) := by
  classical
  simp [chargeScalar, bilinear, unitCharge, Int.cast_sum, Int.cast_mul]

theorem inverseGram_charge_contractions (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (charge : Charge D) (index : Fin D.rank) :
    (∑ original, H original index * chargeScalar D charge original) = (charge index : ℂ) ∧
    (∑ original, H index original * chargeScalar D charge original) = (charge index : ℂ) := by
  classical
  have leftEntry (first second : Fin D.rank) :
      (∑ original, H first original * (D.G original second : ℂ)) =
        if first = second then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply, gramComplex] using
      congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ => matrix first second) leftInverse
  have rightEntry (first second : Fin D.rank) :
      (∑ original, (D.G first original : ℂ) * H original second) =
        if first = second then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply, gramComplex] using
      congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ => matrix first second) rightInverse
  constructor
  · simp_rw [chargeScalar_expansion]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have reordering (coordinateIndex : Fin D.rank) :
        (∑ original, H original index *
          ((D.G original coordinateIndex : ℂ) * (charge coordinateIndex : ℂ))) =
        (∑ original, (D.G coordinateIndex original : ℂ) * H original index) *
          (charge coordinateIndex : ℂ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro original originalMember
      rw [D.symmetric original coordinateIndex]
      ring
    simp_rw [reordering, rightEntry]
    simp
  · simp_rw [chargeScalar_expansion]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have reordering (coordinateIndex : Fin D.rank) :
        (∑ original, H index original *
          ((D.G original coordinateIndex : ℂ) * (charge coordinateIndex : ℂ))) =
        (∑ original, H index original * (D.G original coordinateIndex : ℂ)) *
          (charge coordinateIndex : ℂ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro original originalMember
      ring
    simp_rw [reordering, leftEntry]
    simp

theorem normalSummand_zero_mode_split (D : LatticeData)
    (first second : Fin D.rank) (charge : Charge D) (polynomial : Oscillator D)
    (mode internal : ℤ) (nonzeroMode : mode ≠ 0) :
    normalSummand D first second internal (mode - internal) (Finsupp.single charge polynomial) =
      oscillatorNormalSummand D first second mode internal (Finsupp.single charge polynomial) +
      if internal = 0 then chargeScalar D charge first •
        neutralMode D second mode (Finsupp.single charge polynomial)
      else if internal = mode then chargeScalar D charge second •
        neutralMode D first mode (Finsupp.single charge polynomial) else 0 := by
  by_cases zeroInternal : internal = 0
  · subst internal
    simp only [oscillatorNormalSummand, normalSummand, eq_self_iff_true,
      true_or, if_true, show ¬ (0 : ℤ) < 0 by omega, if_false,
      LinearMap.zero_apply, zero_add, sub_zero, Module.End.mul_apply,
      neutralMode_zero_single, map_smul]
  · by_cases equalMode : internal = mode
    · subst internal
      by_cases negative : mode < 0
      · simp only [oscillatorNormalSummand, normalSummand, eq_self_iff_true,
          or_true, if_true, if_neg nonzeroMode, if_pos negative,
          LinearMap.zero_apply, zero_add, sub_self, Module.End.mul_apply,
          neutralMode_zero_single, map_smul]
      · simp only [oscillatorNormalSummand, normalSummand, eq_self_iff_true,
          or_true, if_true, if_neg nonzeroMode, if_neg negative,
          LinearMap.zero_apply, zero_add, sub_self, Module.End.mul_apply]
        calc
          _ = neutralMode D second 0
              (Finsupp.single charge (neutralPolynomialMode D first charge mode polynomial)) := by
                rw [neutralMode_single]
          _ = chargeScalar D charge second •
              Finsupp.single charge (neutralPolynomialMode D first charge mode polynomial) :=
                neutralMode_zero_single D second charge _
          _ = _ := by rw [neutralMode_single]
    · simp [oscillatorNormalSummand, zeroInternal, equalMode]

theorem normalSummand_finsum_split (D : LatticeData)
    (first second : Fin D.rank) (charge : Charge D) (polynomial : Oscillator D)
    (mode : ℤ) (nonzeroMode : mode ≠ 0) :
    (∑ᶠ internal : ℤ,
      normalSummand D first second internal (mode - internal) (Finsupp.single charge polynomial)) =
    (∑ᶠ internal : ℤ,
      oscillatorNormalSummand D first second mode internal (Finsupp.single charge polynomial)) +
      (chargeScalar D charge first • neutralMode D second mode (Finsupp.single charge polynomial) +
        chargeScalar D charge second • neutralMode D first mode (Finsupp.single charge polynomial)) := by
  classical
  let correction := fun internal : ℤ =>
    if internal = 0 then chargeScalar D charge first •
      neutralMode D second mode (Finsupp.single charge polynomial)
    else if internal = mode then chargeScalar D charge second •
      neutralMode D first mode (Finsupp.single charge polynomial) else 0
  have correctionSupport : Function.support correction ⊆ ({0, mode} : Finset ℤ) := by
    intro internal nonzero
    by_cases atZero : internal = 0
    · simp [atZero]
    · by_cases atMode : internal = mode
      · simp [atMode]
      · exact False.elim (nonzero (by simp [correction, atZero, atMode]))
  have correctionFinite : Function.HasFiniteSupport correction :=
    (Finset.finite_toSet {0, mode}).subset correctionSupport
  have correctionSum : (∑ᶠ internal : ℤ, correction internal) =
      chargeScalar D charge first • neutralMode D second mode (Finsupp.single charge polynomial) +
        chargeScalar D charge second • neutralMode D first mode (Finsupp.single charge polynomial) := by
    rw [finsum_eq_sum_of_support_subset _ correctionSupport]
    simp [correction, nonzeroMode, Ne.symm nonzeroMode]
  have split := finsum_congr (fun internal : ℤ =>
    normalSummand_zero_mode_split D first second charge polynomial mode internal nonzeroMode)
  change (∑ᶠ internal : ℤ, normalSummand D first second internal (mode - internal)
    (Finsupp.single charge polynomial)) = _
  rw [split, finsum_add_distrib
    (oscillatorNormalSummand_finite D first second mode (Finsupp.single charge polynomial))
    correctionFinite, correctionSum]

theorem original_sugawara_charged_separation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (charge : Charge D) (polynomial : Oscillator D) (mode : ℤ) (nonzeroMode : mode ≠ 0) :
    sugawaraMode D H mode (Finsupp.single charge polynomial) =
      directionalCurrent D (fun index => (charge index : ℂ)) mode (Finsupp.single charge polynomial) +
        oscillatorSugawaraMode D H mode (Finsupp.single charge polynomial) := by
  classical
  have firstLinear :
      (∑ first, ∑ second, H first second • (chargeScalar D charge first •
        neutralMode D second mode (Finsupp.single charge polynomial))) =
      directionalCurrent D (fun index => (charge index : ℂ)) mode (Finsupp.single charge polynomial) := by
    simp only [smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have contraction (index : Fin D.rank) :=
      (inverseGram_charge_contractions D H leftInverse rightInverse charge index).1
    simp_rw [contraction]
    simp [directionalCurrent]
  have secondLinear :
      (∑ first, ∑ second, H first second • (chargeScalar D charge second •
        neutralMode D first mode (Finsupp.single charge polynomial))) =
      directionalCurrent D (fun index => (charge index : ℂ)) mode (Finsupp.single charge polynomial) := by
    simp only [smul_smul]
    simp_rw [← Finset.sum_smul]
    have contraction (index : Fin D.rank) :=
      (inverseGram_charge_contractions D H leftInverse rightInverse charge index).2
    simp_rw [contraction]
    simp [directionalCurrent]
  rw [sugawaraMode_finsum]
  have splitFormula (first second : Fin D.rank) :=
    normalSummand_finsum_split D first second charge polynomial mode nonzeroMode
  simp_rw [splitFormula]
  simp only [smul_add, Finset.sum_add_distrib, firstLinear, secondLinear,
    LinearMap.smul_apply]
  let quadratic : Carrier D := ∑ first, ∑ second, H first second •
    ∑ᶠ internal : ℤ, oscillatorNormalSummand D first second mode internal
      (Finsupp.single charge polynomial)
  let linear : Carrier D := directionalCurrent D (fun index => (charge index : ℂ)) mode
    (Finsupp.single charge polynomial)
  change (2 : ℂ)⁻¹ • quadratic + ((2 : ℂ)⁻¹ • linear + (2 : ℂ)⁻¹ • linear) =
    linear + (2 : ℂ)⁻¹ • quadratic
  module

theorem original_tensor_sugawara_charged_separation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (charge : Charge D) (polynomial : Oscillator D) (ghost : Fock ℂ)
    (mode : ℤ) (nonzeroMode : mode ≠ 0) :
    M D H mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) =
      O D (fun index => (charge index : ℂ)) mode (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) +
        oscillatorSugawaraMode D H mode (Finsupp.single charge polynomial) ⊗ₜ[ℂ] ghost := by
  simp only [M, O, TensorProduct.map_tmul, LinearMap.id_apply,
    original_sugawara_charged_separation D H leftInverse rightInverse charge polynomial mode nonzeroMode,
    TensorProduct.add_tmul]

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
