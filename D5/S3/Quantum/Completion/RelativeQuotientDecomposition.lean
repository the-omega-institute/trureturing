/- GID: D5/S3/Quantum/Completion/RelativeQuotientDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RelativeQuotientDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A closed inclusion splits its ambient subspace and identifies the relative quotient. -/

import D5.S3.Quantum.Algebra.QuotientOrthogonalComplement

/- Library-search audit trail (2026-08-20):
   * Repository search found the frozen declaration
     `quotient_orthogonal_complement_isometry`, which proves that Mathlib's
     canonical quotient map is an isometry and a bijection. It is imported
     and directly applied below.
   * Pinned-Mathlib search found the exact constructions
     `Submodule.isCompl_orthogonal` and `Submodule.quotientEquivOrthogonal`.
     They supply the decomposition and canonical isometric equivalence.
   * No repository or pinned-Mathlib theorem was found that packages both
     clauses for an inclusion of two named closed subspaces. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Completion.RelativeQuotientDecomposition

open D5.S3.Quantum.Algebra.QuotientOrthogonalComplement

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The isometric inclusion of a closed subspace `M` into a containing
closed subspace `N`. -/
def subspaceInclusion (M N : ClosedSubmodule 𝕜 E) (hMN : M ≤ N) :
    M.toSubmodule →ₗᵢ[𝕜] N.toSubmodule where
  toLinearMap :=
    { toFun := fun x => ⟨x, hMN x.property⟩
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro c x
        ext
        rfl }
  norm_map' := by
    intro x
    rfl

/-- The copy of `M` inside `N`, constructed as the range of the given
closed-subspace inclusion. -/
def relativeSubspace (M N : ClosedSubmodule 𝕜 E) (hMN : M ≤ N) :
    ClosedSubmodule 𝕜 N.toSubmodule where
  toSubmodule := LinearMap.range (subspaceInclusion M N hMN).toLinearMap
  isClosed' := by
    have hRange :
        LinearMap.range (subspaceInclusion M N hMN).toLinearMap =
          (M.comap N.toSubmodule.subtypeL).toSubmodule := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        refine ⟨⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        rfl
    change IsClosed
      ((LinearMap.range (subspaceInclusion M N hMN).toLinearMap :
        Submodule 𝕜 N.toSubmodule) : Set N.toSubmodule)
    rw [hRange]
    exact (M.comap N.toSubmodule.subtypeL).isClosed

/-- The canonical quotient isometry for the relative inclusion `M ≤ N`. -/
def relativeQuotientIsometry (M N : ClosedSubmodule 𝕜 E) (hMN : M ≤ N) :
    (N.toSubmodule ⧸
        (relativeSubspace M N hMN : Submodule 𝕜 N.toSubmodule)) ≃ₗᵢ[𝕜]
      (relativeSubspace M N hMN : Submodule 𝕜 N.toSubmodule)ᗮ := by
  letI : CompleteSpace N.toSubmodule := N.isClosed.completeSpace_coe
  exact (relativeSubspace M N hMN :
    Submodule 𝕜 N.toSubmodule).quotientEquivOrthogonal

/-- A closed subspace inclusion decomposes the containing subspace into the
included copy and its relative orthogonal complement, while the canonical
relative quotient map is an isometric bijection onto that complement. -/
theorem relative_quotient_orthogonal_decomposition
    (M N : ClosedSubmodule 𝕜 E) (hMN : M ≤ N) :
    IsCompl
        (relativeSubspace M N hMN : Submodule 𝕜 N.toSubmodule)
        (relativeSubspace M N hMN : Submodule 𝕜 N.toSubmodule)ᗮ ∧
      Isometry (relativeQuotientIsometry M N hMN) ∧
      Function.Bijective (relativeQuotientIsometry M N hMN) := by
  letI : CompleteSpace N.toSubmodule := N.isClosed.completeSpace_coe
  let K : Submodule 𝕜 N.toSubmodule := relativeSubspace M N hMN
  have hCanonical := quotient_orthogonal_complement_isometry K
  refine ⟨K.isCompl_orthogonal, ?_, ?_⟩
  · simpa [K, relativeQuotientIsometry] using hCanonical.1
  · simpa [K, relativeQuotientIsometry] using hCanonical.2.1

example : ℝ := 0

example : ∃ (M N : ClosedSubmodule ℝ ℝ), M ≤ N :=
  ⟨⊥, ⊤, bot_le⟩

#print axioms relative_quotient_orthogonal_decomposition

end D5.S3.Quantum.Completion.RelativeQuotientDecomposition
