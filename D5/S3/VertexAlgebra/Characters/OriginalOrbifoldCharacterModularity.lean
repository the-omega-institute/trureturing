/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldCharacterModularity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldCharacterModularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The shifted trace of the actual Golay–Leech orbifold is invariant under SL(2, ℤ). -/

import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter
import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldSectorModularity
import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAmbientModularity

/-! Modular invariance of the literal shifted trace of the original Golay–Leech orbifold. -/

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace D5.S3.VertexAlgebra.OriginalOrbifoldCharacterModularity

open OriginalOrbifoldAnalyticCharacter (ambientCharacter character actual_leech_shifted_character)
open OriginalOrbifoldAmbientModularity (ambientCharacter_s_invariant)
open OriginalOrbifoldSectorModularity (B C D B_eq_eta C_eq_eta D_eq_eta sector_sum_invariant)

/-- The shifted trace is the half-sum of the ambient, signed and two twisted sectors. -/
theorem character_eq_sector_sum (τ : UpperHalfPlane) :
    character τ = (ambientCharacter τ + B τ + C τ + D τ) / 2 := by
  have htrace := actual_leech_shifted_character (τ : ℂ) τ.im_pos
  rw [htrace.2.1, htrace.2.2.1, B_eq_eta, C_eq_eta, D_eq_eta]
  ring

/-- The actual shifted trace is invariant under inversion. -/
theorem character_s_invariant (τ : UpperHalfPlane) :
    character (ModularGroup.S • τ : UpperHalfPlane) = character τ := by
  have hS : (↑(ModularGroup.S • τ) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [neg_div, one_div]
  have hambient :
      ambientCharacter (ModularGroup.S • τ : UpperHalfPlane) = ambientCharacter τ := by
    rw [hS]
    exact ambientCharacter_s_invariant (τ : ℂ) τ.im_pos
  have hsectors := (sector_sum_invariant τ).1
  simp only [add_assoc] at hsectors
  simp only [character_eq_sector_sum, hambient, add_assoc, hsectors]

/-- Translation by one preserves the shifted trace by periodicity of its integer powers. -/
theorem character_t_invariant (τ : UpperHalfPlane) :
    character (ModularGroup.T • τ : UpperHalfPlane) = character τ := by
  have hT : (↑(ModularGroup.T • τ) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]
    simp [add_comm]
  rw [hT]
  exact (actual_leech_shifted_character (τ : ℂ) τ.im_pos).2.2.2

/-- The actual shifted trace is invariant under the weight-zero action of `SL(2, ℤ)`. -/
theorem character_slash_invariant (γ : SL(2, ℤ)) :
    ((fun τ : UpperHalfPlane => character τ) ∣[(0 : ℤ)] γ) =
      (fun τ : UpperHalfPlane => character τ) := by
  apply SlashInvariantForm.slash_action_generators_SL2Z _ _ γ
  · funext τ
    simpa only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one] using
      character_s_invariant τ
  · funext τ
    simpa only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one] using
      character_t_invariant τ

/-- Multiplication by the modular discriminant gives weight-twelve slash invariance. -/
theorem character_mul_discriminant_slash_invariant (γ : SL(2, ℤ)) :
    ((fun τ : UpperHalfPlane => character τ * ModularForm.discriminant τ) ∣[(12 : ℤ)] γ) =
      (fun τ : UpperHalfPlane => character τ * ModularForm.discriminant τ) := by
  change (((fun τ : UpperHalfPlane => character τ) * ModularForm.discriminant)
      ∣[(0 : ℤ) + 12] γ) = (fun τ : UpperHalfPlane => character τ) * ModularForm.discriminant
  rw [ModularForm.mul_slash_SL2, character_slash_invariant,
    SlashInvariantForm.slash_action_generators_SL2Z ModularForm.discriminant_S_invariant
      ModularForm.discriminant_T_invariant γ]

#print axioms character_eq_sector_sum
#print axioms character_s_invariant
#print axioms character_t_invariant
#print axioms character_slash_invariant
#print axioms character_mul_discriminant_slash_invariant

end D5.S3.VertexAlgebra.OriginalOrbifoldCharacterModularity
