/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldMoonshineCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldMoonshineCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Golay–Leech orbifold character is E₄³/Δ − 744. -/

import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldCharacterModularity
import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldCuspExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-! The moonshine character of the original Golay–Leech orbifold. -/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace D5.S3.VertexAlgebra.OriginalOrbifoldMoonshineCharacter

open ModularForm (E₄ discriminant)
open OriginalOrbifoldAnalyticCharacter (character)
open OriginalOrbifoldCharacterModularity (character_mul_discriminant_slash_invariant)
open OriginalOrbifoldCuspExpansion (weightedCharacter_holomorphic weightedCharacter_bounded
  weightedCharacter_sub_eisensteinCube_qExpansion)

local notation "weightedTrace" => (fun τ : ℍ => character τ * discriminant τ)

/-- The literal shifted trace times the discriminant, bundled at weight twelve. -/
private def weightedTraceForm : ModularForm 𝒮ℒ 12 where
  toFun := weightedTrace
  slash_action_eq' γ hγ := by
    obtain ⟨γ, rfl⟩ := hγ
    exact character_mul_discriminant_slash_invariant γ
  holo' := weightedCharacter_holomorphic
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [character_mul_discriminant_slash_invariant]
    exact weightedCharacter_bounded

/-- The literal shifted trace of the constructed Golay–Leech orbifold equals `j − 744`
at every point of the upper half-plane. -/
theorem character_eq_eisensteinCube_div_discriminant_sub_744 (τ : ℍ) :
    character τ = E₄ τ ^ (3 : ℕ) / discriminant τ - 744 := by
  let f : ModularForm 𝒮ℒ 12 := weightedTraceForm - ModularForm.mcast (by decide) (E₄.pow 3)
  have hf : (f : ℍ → ℂ) = weightedTrace - (fun z : ℍ => E₄ z ^ (3 : ℕ)) := by
    simp only [f, FunLike.coe_sub, ModularForm.coe_mcast, ModularForm.coe_pow]
    rfl
  have hcoeff : (qExpansion 1 f).coeff 0 = 0 ∧ (qExpansion 1 f).coeff 1 = -744 := by
    rw [hf]
    exact weightedCharacter_sub_eisensteinCube_qExpansion
  let g := ModularForm.toCuspForm f hcoeff.1
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hg : (g : ℍ → ℂ) = f := rfl
  have hcFun : (c • CuspForm.discriminant : ℍ → ℂ) = g := congrArg DFunLike.coe hc
  have hq := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c CuspForm.discriminant
  rw [hcFun, hg] at hq
  have hcVal : c = -744 := by
    simpa only [hcoeff.2, PowerSeries.coeff_smul, CuspForm.coe_discriminant,
      ModularForm.discriminant_qExpansion_coeff_one, smul_eq_mul, mul_one] using
      (congrArg (fun p : PowerSeries ℂ => p.coeff 1) hq).symm
  have hcτ : c * discriminant τ = f τ := congrFun hcFun τ
  have hfτ : f τ = character τ * discriminant τ - E₄ τ ^ (3 : ℕ) := congrFun hf τ
  rw [hcVal, hfτ] at hcτ
  rw [eq_sub_iff_add_eq, eq_div_iff (ModularForm.discriminant_ne_zero τ)]
  linear_combination -hcτ

#print axioms character_eq_eisensteinCube_div_discriminant_sub_744

end D5.S3.VertexAlgebra.OriginalOrbifoldMoonshineCharacter
