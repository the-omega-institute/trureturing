import D5.S3.Arith.ModularForms.RademacherLinearCutoffRate
import D5.S3.Geometry.AdS3.AdS3MarkedQuadraticTail

/-!
# Compact-uniform rate for the marked AdS₃ filling character

The error of the normalized geometric cutoff is the sum of its linear and
quadratic errors. The polar seed cancels in the exact decomposition.
-/

set_option autoImplicit false

open scoped BigOperators UpperHalfPlane

namespace D5.S3.Geometry.AdS3MarkedFillingCharacter

open D5.S3.Arith.ModularForms.RademacherLinearTailConvergence
  (norm_linearPrincipalValueQTailLimit_sub_linearCutoff_sub_twelve_le)
open D5.S3.VertexAlgebra.ActualLeechOrbifoldTraceSeries (character)

/-- On a compact set the actual marked filling sum, shifted by twelve,
approximates the graded-dimension Leech character with error at most
`C * N ^ (-1/8)` once `N ≥ 2 * (B + 1)`, where `B` bounds `‖τ‖` on the set. -/
theorem norm_character_sub_markedFillingCutoff_sub_twelve_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ (∀ τ ∈ K, ‖(τ : ℂ)‖ ≤ B) ∧
      ∀ τ ∈ K, ∀ N : ℕ, 2 * (B + 1) ≤ (N : ℝ) →
        ‖character τ - ((∑ m ∈ markedFillingCutoff τ N, markedFillingVacuumSummand τ m) - 12)‖ ≤
          C * (N : ℝ) ^ (-(1 / 8) : ℝ) := by
  obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image
    (continuous_norm.comp UpperHalfPlane.continuous_coe).continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hnorm (τ : ℍ) (hτ : τ ∈ K) : ‖(τ : ℂ)‖ ≤ B :=
    (hB₀ (Set.mem_image_of_mem _ hτ)).trans (le_max_left _ _)
  obtain ⟨_, δ, hδ, hstrip⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  obtain ⟨CL, hCL, hlinear⟩ :=
    norm_linearPrincipalValueQTailLimit_sub_linearCutoff_sub_twelve_le hδ hB
  obtain ⟨CQ, hCQ, hquad⟩ := norm_markedFillingQuadratic_tsum_sub_cutoff_le hK
  refine ⟨B, CL + CQ, hB, add_pos hCL hCQ, hnorm, fun τ hτ N hN => ?_⟩
  have hN' : (1 : ℝ) ≤ N := by linarith
  have hN₁ : 1 ≤ N := by exact_mod_cast hN'
  have hquadratic : CQ / (N : ℝ) ^ 2 ≤ CQ * (N : ℝ) ^ (-(1 / 8) : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_two, ← Real.rpow_neg (Nat.cast_nonneg N)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN' (by norm_num)) hCQ.le
  rw [character_sub_markedFillingCutoff_sub_twelve, add_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (hlinear τ (hstrip hτ).2 (hnorm τ hτ) N hN)
      ((hquad τ hτ N hN₁).trans hquadratic))

end D5.S3.Geometry.AdS3MarkedFillingCharacter
