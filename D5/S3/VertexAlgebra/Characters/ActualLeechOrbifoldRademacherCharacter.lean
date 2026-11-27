/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldRademacherCharacter
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Leech orbifold character as the normalized rectangular Rademacher limit. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Arith.ModularForms.RademacherAnchoredS
import D5.S3.Arith.ModularForms.RademacherLimitAnalysis
import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldHeckeExpansion
import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldMoonshineCharacter
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# The rectangular Rademacher limit is the actual Leech character

The genuine dimension series gives the same principal part at infinity as the
independent rectangular limit. Their holomorphic, level-one invariant
difference is bounded at the cusp and its constant value is zero.
-/

open Filter UpperHalfPlane ModularForm
open scoped BigOperators Manifold MatrixGroups ModularForm Topology UpperHalfPlane

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldRademacherCharacter

open D5.S3.Arith.ModularForms.RademacherVacuum (rademacherCutoff)
open D5.S3.Arith.ModularForms.RademacherRectangularConvergence
  (rademacherLimit rademacherLimit_one_vadd tendstoLocallyUniformly_rademacherCutoff_sub_twelve)
open D5.S3.Arith.ModularForms.RademacherAnchoredS (rademacherLimit_S_smul)
open D5.S3.Arith.ModularForms.RademacherLimitAnalysis
  (mdifferentiable_rademacherLimit tendsto_rademacherLimit_sub_pole_atImInfty)
open ActualLeechOrbifoldTraceSeries (dimension character graded_dimension_series)
open ActualLeechOrbifoldMoonshineCharacter (character_eq_j_sub_744)
open private low_dimensions from D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldHeckeExpansion

set_option autoImplicit false

noncomputable section

local notation "𝕢" => Function.Periodic.qParam 1

private theorem cancel_pole_term (τ : ℍ) (n : ℕ) :
    (𝕢 (τ : ℂ))⁻¹ * ((dimension (n + 2 : ℕ) : ℂ) * 𝕢 (τ : ℂ) ^ (n + 2)) =
      (dimension (n + 2 : ℕ) : ℂ) * 𝕢 (τ : ℂ) ^ (n + 1) := by
  let q := 𝕢 (τ : ℂ)
  have hq : q ≠ 0 := Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)
  change q⁻¹ * ((dimension (n + 2 : ℕ) : ℂ) * q ^ (n + 2)) = _
  rw [show q ^ (n + 2) = q ^ (n + 1) * q by exact pow_succ q (n + 1)]
  calc
    q⁻¹ * ((dimension (n + 2 : ℕ) : ℂ) * (q ^ (n + 1) * q)) =
        (q⁻¹ * q) * ((dimension (n + 2 : ℕ) : ℂ) * q ^ (n + 1)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hq, one_mul]

private theorem character_sub_pole_eq_tsum (τ : ℍ) :
    character τ - (𝕢 (τ : ℂ))⁻¹ =
      ∑' n : ℕ, (dimension (n + 2 : ℕ) : ℂ) * 𝕢 (τ : ℂ) ^ (n + 1) := by
  let a (n : ℕ) := (dimension n : ℂ) * 𝕢 (τ : ℂ) ^ n
  have hs : Summable a := (graded_dimension_series τ).1.of_norm
  have hsplit : 1 + (∑' n : ℕ, a (n + 2)) = ∑' n : ℕ, a n := by
    have ha₀ : a 0 = 1 := by simp [a, low_dimensions.1]
    have ha₁ : a 1 = 0 := by simp [a, low_dimensions.2]
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, ha₀, ha₁, zero_add, add_zero]
      using hs.sum_add_tsum_nat_add 2
  change (𝕢 (τ : ℂ))⁻¹ * (∑' n : ℕ, a n) - (𝕢 (τ : ℂ))⁻¹ = _
  rw [← hsplit, mul_add, mul_one, add_sub_cancel_left, ← tsum_mul_left]
  exact tsum_congr (cancel_pole_term τ)

/-- The dimension series has zero limit once the weight-zero vacuum pole is removed.
Absolute summability at i supplies a common majorant near the cusp. -/
theorem tendsto_character_sub_pole_atImInfty :
    Tendsto (fun τ : ℍ => character τ - (𝕢 (τ : ℂ))⁻¹) atImInfty (𝓝 0) := by
  let term (τ : ℍ) (n : ℕ) := (dimension (n + 2 : ℕ) : ℂ) * 𝕢 (τ : ℂ) ^ (n + 1)
  let i : ℍ := UpperHalfPlane.I
  have hsum : Summable (fun n : ℕ => ‖term i n‖) := by
    have hshift := (summable_nat_add_iff
      (f := fun n : ℕ => ‖(dimension n : ℂ) * 𝕢 (i : ℂ) ^ n‖) 2).mpr
      (graded_dimension_series i).1
    apply (hshift.mul_left ‖(𝕢 (i : ℂ))⁻¹‖).congr
    intro n
    rw [← norm_mul, cancel_pole_term i n]
  have hq := qParam_tendsto_atImInfty (h := 1) zero_lt_one
  have hvanish (n : ℕ) : Tendsto (fun τ => term τ n) atImInfty (𝓝 0) := by
    simpa only [term, zero_pow (Nat.succ_ne_zero n), mul_zero] using
      (hq.pow (n + 1)).const_mul (dimension (n + 2 : ℕ) : ℂ)
  have hi : 0 < ‖𝕢 (i : ℂ)‖ :=
    norm_pos_iff.mpr (Function.Periodic.qParam_ne_zero (h := 1) (i : ℂ))
  have hdom : ∀ᶠ τ in atImInfty, ∀ n : ℕ, ‖term τ n‖ ≤ ‖term i n‖ := by
    have he : ∀ᶠ τ : ℍ in atImInfty, ‖𝕢 (τ : ℂ)‖ < ‖𝕢 (i : ℂ)‖ := by
      simpa only [dist_zero_right] using Metric.tendsto_nhds.mp hq _ hi
    filter_upwards [he] with τ hτ n
    simp only [term, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hτ.le _) (norm_nonneg _)
  have h := tendsto_tsum_of_dominated_convergence
    (g := fun _ : ℕ => (0 : ℂ)) hsum hvanish hdom
  simpa only [tsum_zero] using h.congr (fun τ => (character_sub_pole_eq_tsum τ).symm)

private theorem mdifferentiable_character : MDiff character := by
  have hΔ : MDiff ModularForm.discriminant := CuspForm.discriminant.holo'
  have hj := (E₄.holo'.pow 3).div hΔ discriminant_ne_zero
  rw [show character = (fun τ : ℍ => E₄ τ ^ (3 : ℕ) / ModularForm.discriminant τ - 744)
    from funext character_eq_j_sub_744]
  exact hj.sub mdifferentiable_const

private theorem character_SL_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    character (γ • τ) = character τ := by
  have hγ : Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hE := SlashInvariantForm.slash_action_eqn'' E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  change E₄ (γ • τ) = _ at hE
  change CuspForm.discriminant (γ • τ) = _ at hΔ
  rw [character_eq_j_sub_744, character_eq_j_sub_744]
  change E₄ (γ • τ) ^ (3 : ℕ) / CuspForm.discriminant (γ • τ) - 744 =
    E₄ τ ^ (3 : ℕ) / CuspForm.discriminant τ - 744
  rw [hE, hΔ]
  simp only [zpow_ofNat, mul_pow, ← pow_mul]
  rw [show (4 : ℕ) * 3 = 12 by decide, mul_div_mul_left _ _
    (pow_ne_zero _ (denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ))]

private def characterDifference (τ : ℍ) : ℂ := rademacherLimit τ - character τ

private theorem characterDifference_slash (γ : SL(2, ℤ)) :
    characterDifference ∣[(0 : ℤ)] γ = characterDifference := by
  apply SlashInvariantForm.slash_action_generators_SL2Z ?_ ?_ γ
  · funext τ
    simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one,
      characterDifference, rademacherLimit_S_smul, character_SL_smul]
  · funext τ
    simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one, characterDifference]
    rw [character_SL_smul, modular_T_smul, rademacherLimit_one_vadd]

private theorem tendsto_characterDifference : Tendsto characterDifference atImInfty (𝓝 0) := by
  have h := tendsto_rademacherLimit_sub_pole_atImInfty.sub tendsto_character_sub_pole_atImInfty
  have heq (τ : ℍ) :
      (rademacherLimit τ - (𝕢 (τ : ℂ))⁻¹) - (character τ - (𝕢 (τ : ℂ))⁻¹) =
        characterDifference τ := by
    unfold characterDifference
    abel
  simpa only [sub_zero] using h.congr heq

private def characterDifferenceForm : ModularForm 𝒮ℒ 0 where
  toFun := characterDifference
  slash_action_eq' g hg := by
    obtain ⟨γ, rfl⟩ := hg
    exact characterDifference_slash γ
  holo' := mdifferentiable_rademacherLimit.sub mdifferentiable_character
  bdd_at_cusps' hc := by
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
    intro γ _
    rw [characterDifference_slash]
    exact (show IsZeroAtImInfty characterDifference from
      tendsto_characterDifference).isBoundedAtImInfty

/-- The independent rectangular limit equals the actual Leech orbifold character. -/
theorem rademacherLimit_eq_character (τ : ℍ) : rademacherLimit τ = character τ := by
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const characterDifferenceForm
  change characterDifference = Function.const ℍ c at hc
  have hc₀ : c = 0 := by
    have h : Tendsto (Function.const ℍ c) atImInfty (𝓝 0) := hc ▸ tendsto_characterDifference
    exact tendsto_nhds_unique
      (tendsto_const_nhds : Tendsto (Function.const ℍ c) atImInfty (𝓝 c)) h
  apply sub_eq_zero.mp
  change characterDifference τ = 0
  rw [hc, Function.const_apply, hc₀]

/-- The specified strict rectangles, with the constant 12 removed, converge
locally uniformly to the literal graded-dimension character. -/
theorem tendstoLocallyUniformly_rademacherCutoff_sub_twelve_character :
    TendstoLocallyUniformly (fun N τ => rademacherCutoff N τ - 12) character atTop :=
  tendstoLocallyUniformly_rademacherCutoff_sub_twelve.congr_right rademacherLimit_eq_character

end

end D5.S3.VertexAlgebra.ActualLeechOrbifoldRademacherCharacter
