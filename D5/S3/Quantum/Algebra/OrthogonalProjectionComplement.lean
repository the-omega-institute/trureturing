/- GID: D5/S3/Quantum/Algebra/OrthogonalProjectionComplement
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OrthogonalProjectionComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complementary orthogonal projections satisfy the six canonical operator identities. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/- Library-search audit trail (2026-08-16):
   * Repository search found no existing declaration bundling all six projection identities.
   * Loogle returned exact hits for `Submodule.starProjection_orthogonal`,
     `Submodule.id_eq_sum_starProjection_self_orthogonalComplement`,
     `Submodule.isIdempotentElem_starProjection`, and
     `Submodule.IsOrtho.starProjection_comp_starProjection`.
   * Loogle's shape query `starProjection ∘L starProjection = 0` did not elaborate because the
     unqualified identifier was unknown; it suggested the namespaced projection declaration.
   * LeanSearch API queries were unavailable at the attempted endpoint (HTTP 404).
   * Pinned-Mathlib search confirmed the exact declarations above and
     `Submodule.starProjection_comp_starProjection_of_le`; they are applied directly below. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Algebra.OrthogonalProjectionComplement

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The projections onto a closed subspace and its orthogonal complement are complementary
idempotents: each squares to itself, their two ordered products vanish, and they sum to the
identity. -/
theorem orthogonal_complement_projection_identities
    (M : Submodule 𝕜 E) [IsClosed (M : Set E)] :
    Mᗮ.starProjection = ContinuousLinearMap.id 𝕜 E - M.starProjection ∧
      M.starProjection ∘L M.starProjection = M.starProjection ∧
      Mᗮ.starProjection ∘L Mᗮ.starProjection = Mᗮ.starProjection ∧
      M.starProjection ∘L Mᗮ.starProjection = 0 ∧
      Mᗮ.starProjection ∘L M.starProjection = 0 ∧
      M.starProjection + Mᗮ.starProjection = ContinuousLinearMap.id 𝕜 E := by
  letI : M.HasOrthogonalProjection := inferInstance
  refine ⟨Submodule.starProjection_orthogonal M, ?_, ?_, ?_, ?_, ?_⟩
  · exact Submodule.starProjection_comp_starProjection_of_le (U := M) (V := M) le_rfl
  · exact Submodule.starProjection_comp_starProjection_of_le (U := Mᗮ) (V := Mᗮ) le_rfl
  · exact (Submodule.isOrtho_orthogonal_right M).starProjection_comp_starProjection
  · exact (Submodule.isOrtho_orthogonal_left M).starProjection_comp_starProjection
  · exact (Submodule.id_eq_sum_starProjection_self_orthogonalComplement (K := M)).symm

example : ℝ := 0

example :
    (⊥ : Submodule ℝ ℝ)ᗮ.starProjection =
      ContinuousLinearMap.id ℝ ℝ - (⊥ : Submodule ℝ ℝ).starProjection := by
  letI : IsClosed (((⊥ : Submodule ℝ ℝ) : Set ℝ)) := isClosed_singleton
  exact (orthogonal_complement_projection_identities (M := (⊥ : Submodule ℝ ℝ))).1

#print axioms orthogonal_complement_projection_identities

end D5.S3.Quantum.Algebra.OrthogonalProjectionComplement
