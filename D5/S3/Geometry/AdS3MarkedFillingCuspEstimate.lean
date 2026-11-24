/- GID: D5/S3/Geometry/AdS3MarkedFillingCuspEstimate
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform geometric cusp estimate for the actual Leech graded-dimension character. -/

import D5.S3.Geometry.AdS3MarkedFillingCharacter
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldWeightTwo

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology UpperHalfPlane

namespace D5.S3.Geometry.AdS3MarkedFillingCharacter

open D5.S3.VertexAlgebra.ActualLeechOrbifoldTraceSeries
  (character dimension graded_dimension_series)
open D5.S3.VertexAlgebra.ActualLeechOrbifoldWeightTwo (weight_two_finrank)
open D5.S3.VertexAlgebra.ActualLeechOrbifoldMatter (mode Orbifold)
open private character_sub_pole_eq_tsum character_SL_smul from
  D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldRademacherCharacter

noncomputable section

local notation "𝕢" => Function.Periodic.qParam 1

/-- The inverse multiplier of any marked completion is the reciprocal nome
of its transformed modulus. -/
theorem rawBoltzmann_eq_inv_qParam (γ : SL(2, ℤ)) (τ : ℍ) :
    rawBoltzmann γ τ = (𝕢 (↑(γ • τ) : ℂ))⁻¹ := by
  rw [← rawBoltzmann_one (γ • τ)]
  simp only [rawBoltzmann, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The weight-two coefficient is the dimension of the assembled stress eigenspace. -/
theorem dimension_two : dimension 2 = 196884 := by
  have hcast : ((2 : ℤ) : ℂ) = 2 := by norm_num
  have he := congrArg (fun z : ℂ => Module.finrank ℂ
    (Module.End.eigenspace (M := Orbifold) (mode 0) z)) hcast
  exact he.trans weight_two_finrank

private theorem summable_shifted_dimension (τ : ℍ) (k : ℕ) :
    Summable (fun n : ℕ => ‖(dimension (n + k : ℕ) : ℂ) * 𝕢 (τ : ℂ) ^ n‖) := by
  let q := 𝕢 (τ : ℂ)
  have hq := Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)
  have hs := (summable_nat_add_iff
    (f := fun n : ℕ => ‖(dimension n : ℂ) * q ^ n‖) k).mpr
    (graded_dimension_series τ).1
  apply (hs.mul_right ‖(q ^ k)⁻¹‖).congr
  intro n
  rw [← norm_mul, pow_add]
  congr 1
  rw [← mul_assoc, mul_inv_cancel_right₀ (pow_ne_zero k hq)]

/-- The normalized tail has a finite common majorant at the reference modulus i. -/
def cuspTailConstant : ℝ :=
  ∑' n : ℕ, ‖(dimension (n + 3 : ℕ) : ℂ) * 𝕢 (↑UpperHalfPlane.I : ℂ) ^ n‖

theorem cuspTailConstant_nonneg : 0 ≤ cuspTailConstant :=
  tsum_nonneg (fun _ => norm_nonneg _)

private theorem character_sub_pole_sub_weight_two (τ : ℍ) :
    character τ - (𝕢 (τ : ℂ))⁻¹ - 196884 * 𝕢 (τ : ℂ) =
      (∑' n : ℕ, (dimension (n + 3 : ℕ) : ℂ) * 𝕢 (τ : ℂ) ^ n) * 𝕢 (τ : ℂ) ^ 2 := by
  let q := 𝕢 (τ : ℂ)
  let f (n : ℕ) := (dimension (n + 2 : ℕ) : ℂ) * q ^ (n + 1)
  have hs : Summable f := by
    simpa only [f, pow_succ, ← mul_assoc] using
      ((summable_shifted_dimension τ 2).of_norm.mul_right q)
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hzero : f 0 = 196884 * q := by norm_num [f, dimension_two]
  simp only [Finset.sum_range_one, hzero] at hsplit
  rw [character_sub_pole_eq_tsum]
  change (∑' n, f n) - 196884 * q = _
  rw [← hsplit, add_sub_cancel_left, ← tsum_mul_right]
  apply tsum_congr
  intro n
  change (dimension (n + 3 : ℕ) : ℂ) * q ^ (n + 2) =
    (dimension (n + 3 : ℕ) : ℂ) * q ^ n * q ^ 2
  rw [pow_add, mul_assoc]

private theorem norm_qParam_le_reference (z : ℍ) (hz : 1 ≤ z.im) :
    ‖𝕢 (z : ℂ)‖ ≤ ‖𝕢 (↑UpperHalfPlane.I : ℂ)‖ := by
  rw [Function.Periodic.norm_qParam, Function.Periodic.norm_qParam, Real.exp_le_exp]
  simp only [div_one, UpperHalfPlane.coe_im, UpperHalfPlane.I_im, mul_one]
  simpa only [mul_one] using
    mul_le_mul_of_nonpos_left hz (show -2 * Real.pi ≤ 0 by linarith [Real.pi_pos])

private theorem norm_qParam_eq_exp_neg_core (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖𝕢 (↑(γ • τ) : ℂ)‖ = Real.exp (-coreTranslationLength γ τ) := by
  have he := norm_rawBoltzmann γ τ
  rw [rawBoltzmann_eq_inv_qParam, norm_inv] at he
  rw [Real.exp_neg, ← he, inv_inv]

/-- Uniform genus-one cusp estimate for every modular completion whose
transformed height is at least one, with the actual core displacement in
the exponential error. -/
theorem norm_character_sub_rawBoltzmann_sub_weight_two_le
    (γ : SL(2, ℤ)) (τ : ℍ) (h : 1 ≤ (γ • τ).im) :
    ‖character τ - rawBoltzmann γ τ - 196884 * 𝕢 (↑(γ • τ) : ℂ)‖ ≤
      cuspTailConstant * Real.exp (-2 * coreTranslationLength γ τ) := by
  let z := γ • τ
  let q := 𝕢 (z : ℂ)
  have hq : ‖q‖ = Real.exp (-coreTranslationLength γ τ) :=
    norm_qParam_eq_exp_neg_core γ τ
  have hdom (n : ℕ) :
      ‖(dimension (n + 3 : ℕ) : ℂ) * q ^ n‖ ≤
        ‖(dimension (n + 3 : ℕ) : ℂ) * 𝕢 (↑UpperHalfPlane.I : ℂ) ^ n‖ := by
    simp only [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_qParam_le_reference z h) _) (norm_nonneg _)
  have hsum :
      ‖∑' n : ℕ, (dimension (n + 3 : ℕ) : ℂ) * q ^ n‖ ≤ cuspTailConstant :=
    (norm_tsum_le_tsum_norm (summable_shifted_dimension z 3)).trans
      (Summable.tsum_le_tsum hdom (summable_shifted_dimension z 3)
        (summable_shifted_dimension UpperHalfPlane.I 3))
  rw [← character_SL_smul γ τ, rawBoltzmann_eq_inv_qParam,
    character_sub_pole_sub_weight_two, norm_mul, norm_pow]
  change ‖∑' n : ℕ, (dimension (n + 3 : ℕ) : ℂ) * q ^ n‖ * ‖q‖ ^ 2 ≤ _
  calc
    _ ≤ cuspTailConstant * ‖q‖ ^ 2 := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by rw [hq, ← Real.exp_nat_mul]; norm_num

/-- A single nonnegative constant works for all marked modular completions. -/
theorem exists_uniform_geometric_cusp_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : SL(2, ℤ)) (τ : ℍ), 1 ≤ (γ • τ).im →
      ‖character τ - rawBoltzmann γ τ - 196884 * 𝕢 (↑(γ • τ) : ℂ)‖ ≤
        C * Real.exp (-2 * coreTranslationLength γ τ) :=
  ⟨cuspTailConstant, cuspTailConstant_nonneg,
    norm_character_sub_rawBoltzmann_sub_weight_two_le⟩

/-- At the actual cusp the first nonpolar coefficient is sharp. -/
theorem tendsto_character_sub_rawBoltzmann_div_qParam :
    Tendsto (fun τ : ℍ => (character τ - rawBoltzmann 1 τ) / 𝕢 (τ : ℂ))
      atImInfty (𝓝 (196884 : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun τ : ℍ => cuspTailConstant * ‖𝕢 (τ : ℂ)‖)
      atImInfty (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using
      (qParam_tendsto_atImInfty (h := 1) zero_lt_one).norm.const_mul cuspTailConstant
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  have hheight : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im :=
    (atImInfty_mem _).mpr ⟨1, fun _ h => h⟩
  filter_upwards [hheight] with τ hτ
  let q := 𝕢 (τ : ℂ)
  have hq0 : q ≠ 0 := Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)
  have hq : ‖q‖ = Real.exp (-coreTranslationLength 1 τ) := by
    simpa only [one_smul] using norm_qParam_eq_exp_neg_core 1 τ
  have hgeom := norm_character_sub_rawBoltzmann_sub_weight_two_le 1 τ (by simpa using hτ)
  have hpow : Real.exp (-2 * coreTranslationLength 1 τ) = ‖q‖ ^ 2 := by
    rw [hq, ← Real.exp_nat_mul]
    norm_num
  simp only [one_smul, hpow] at hgeom
  change ‖(character τ - rawBoltzmann 1 τ) / q - 196884‖ ≤ cuspTailConstant * ‖q‖
  rw [← mul_div_cancel_right₀ (196884 : ℂ) hq0, ← sub_div, norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hq0)).2
  simpa only [pow_two, ← mul_assoc] using hgeom

end
end D5.S3.Geometry.AdS3MarkedFillingCharacter

#check D5.S3.Geometry.AdS3MarkedFillingCharacter.exists_uniform_geometric_cusp_bound
#print axioms D5.S3.Geometry.AdS3MarkedFillingCharacter.dimension_two
#print axioms D5.S3.Geometry.AdS3MarkedFillingCharacter.norm_character_sub_rawBoltzmann_sub_weight_two_le
#print axioms D5.S3.Geometry.AdS3MarkedFillingCharacter.exists_uniform_geometric_cusp_bound

#check D5.S3.Geometry.AdS3MarkedFillingCharacter.tendsto_character_sub_rawBoltzmann_div_qParam
#print axioms D5.S3.Geometry.AdS3MarkedFillingCharacter.tendsto_character_sub_rawBoltzmann_div_qParam
