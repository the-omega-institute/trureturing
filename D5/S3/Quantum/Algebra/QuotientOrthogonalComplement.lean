/- GID: D5/S3/Quantum/Algebra/QuotientOrthogonalComplement
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/QuotientOrthogonalComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical quotient isometrically identifies the orthogonal complement. -/

import Mathlib.Analysis.InnerProductSpace.ProdL2

/- Library-search audit trail (2026-08-15):
   * Repository search for quotient/orthogonal-complement equivalences found no D5 declaration.
   * Loogle query `Submodule.quotientEquivOrthogonal` returned the exact Mathlib definition
     together with its application and coercion lemmas.
   * LeanSearch query `Submodule.quotientEquivOrthogonal` returned related quotient-complement
     equivalences but did not return the exact declaration among its first ten results.
   * Pinned-Mathlib search found the exact definition `Submodule.quotientEquivOrthogonal`,
     imported and applied below; the complementary-projection identity supplies its formula. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Algebra.QuotientOrthogonalComplement

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The canonical map from a subspace quotient to its orthogonal complement is an isometric
equivalence and sends the class of `x` to the component `x - P_K x`. -/
theorem quotient_orthogonal_complement_isometry
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    Isometry (K.quotientEquivOrthogonal : (E ⧸ K) -> Kᗮ) ∧
      Function.Bijective (K.quotientEquivOrthogonal : (E ⧸ K) -> Kᗮ) ∧
      ∀ x : E,
        (K.quotientEquivOrthogonal (Submodule.Quotient.mk x) : E) =
          x - K.starProjection x := by
  refine ⟨K.quotientEquivOrthogonal.isometry,
    EquivLike.bijective K.quotientEquivOrthogonal, ?_⟩
  intro x
  rw [Submodule.coe_quotientEquivOrthogonal]
  change (Kᗮ).projection K K.isCompl_orthogonal.symm x =
    x - K.projection Kᗮ K.isCompl_orthogonal x
  exact Submodule.projection_eq_self_sub_projection K.isCompl_orthogonal x

example : ℝ := 0

example : (⊥ : Submodule ℝ ℝ).HasOrthogonalProjection := inferInstance

#print axioms quotient_orthogonal_complement_isometry

end D5.S3.Quantum.Algebra.QuotientOrthogonalComplement
