/- GID: D5/S3/Observer/Completion/FiniteSubspaceComplementAbsorption
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/FiniteSubspaceComplementAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Removing a finite subspace preserves infinite Hilbert dimension and unitary type. -/

/- Library-search audit trail (2026-08-29):
   * Repository searches found the frozen `basisPrefix`, `basisResidual`, and `tailBasis`
     construction and the canonical quotient/orthogonal-complement isometry, but no theorem for
     an arbitrary finite-dimensional subspace of an infinite-dimensional Hilbert space.
   * Pinned Mathlib exact hits `Orthonormal.exists_hilbertBasis_extension`,
     `Cardinal.mk_compl_of_infinite`, `Submodule.quotientEquivOrthogonal`, and
     `stdOrthonormalBasis` are applied below.
   * Searches for a packaged infinite Hilbert-dimension finite-complement theorem and an
     infinite `HilbertBasis.reindex` returned no exact declaration. -/

import D5.S3.Quantum.Algebra.QuotientOrthogonalComplement
import D5.S3.Quantum.Completion.TransfiniteBasisResidualTower
import Mathlib.SetTheory.Cardinal.Arithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Cardinal
open scoped InnerProductSpace

namespace D5.S3.Observer.Completion.FiniteSubspaceComplementAbsorption

universe u

open D5.S3.Quantum.Completion.TransfiniteBasisResidualTower

/-- If an infinite Hilbert basis indexes `H` and `M` is finite-dimensional, then `M`'s
orthogonal complement has a Hilbert basis with the same index. The resulting basis
classification gives a unitary from the complement to `H`; composing the canonical
quotient/complement isometry gives a unitary from `H / M` to `H`. -/
theorem finite_subspace_complement_absorption
    {K H : Type u} [RCLike K] [NormedAddCommGroup H]
    [InnerProductSpace K H] [CompleteSpace H]
    (M : Submodule K H) [FiniteDimensional K M]
    (hInfinite : ¬FiniteDimensional K H) :
    exists dimensionIndex : Type u,
      exists complementBasis : HilbertBasis dimensionIndex K Mᗮ,
        exists ambientBasis : HilbertBasis dimensionIndex K H,
          exists complementUnitary : Mᗮ ≃ₗᵢ[K] H,
            exists quotientUnitary : (H ⧸ M) ≃ₗᵢ[K] H,
              complementUnitary = complementBasis.repr.trans ambientBasis.repr.symm /\
                quotientUnitary = M.quotientEquivOrthogonal.trans complementUnitary := by
  let mBasis : OrthonormalBasis (Fin (Module.finrank K M)) K M :=
    stdOrthonormalBasis K M
  let sourceVectors : Fin (Module.finrank K M) → H := fun i => mBasis i
  have hSourceOrthonormal : Orthonormal K sourceVectors := by
    apply M.subtypeₗᵢ.orthonormal_comp_iff.mpr
    exact mBasis.orthonormal
  obtain ⟨W, ambientBasis, hSourceSubset, hAmbientBasis⟩ :=
    hSourceOrthonormal.toSubtypeRange.exists_hilbertBasis_extension
  let removed : Set W := Subtype.val ⁻¹' Set.range sourceVectors
  have hRemovedFinite : removed.Finite :=
    (Set.finite_range sourceVectors).preimage Subtype.val_injective.injOn
  have hAmbientInfinite : Infinite W := by
    refine ⟨fun hFinite => ?_⟩
    letI : Finite W := hFinite
    letI : Fintype W := Fintype.ofFinite W
    exact hInfinite ambientBasis.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  letI : Infinite W := hAmbientInfinite
  have hBasisImage : ambientBasis '' removed = Set.range sourceVectors := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hAmbientBasis]
      exact hw
    · rintro ⟨i, rfl⟩
      let w : W := ⟨sourceVectors i, hSourceSubset ⟨i, rfl⟩⟩
      refine ⟨w, ?_, ?_⟩
      · exact ⟨i, rfl⟩
      · simpa [w] using congrFun hAmbientBasis w
  have hSourceSpan : Submodule.span K (Set.range sourceVectors) = M := by
    apply (M.span_range_subtype_eq_top_iff (fun i => (mBasis i).2)).mp
    simpa [sourceVectors] using mBasis.toBasis.span_eq.ge
  have hPrefix : (basisPrefix ambientBasis removed).toSubmodule = M := by
    rw [basisPrefix, hBasisImage, hSourceSpan]
    exact M.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  have hResidual : (basisResidual ambientBasis removed).toSubmodule = Mᗮ := by
    rw [basisResidual, ClosedSubmodule.toSubmodule_orthogonal_eq, hPrefix]
  let remainingBasis : HilbertBasis ↥(removedᶜ) K Mᗮ :=
    hResidual ▸ tailBasis ambientBasis removed
  have hRemovedSmall : #removed < #W :=
    (Cardinal.mk_lt_aleph0_iff.mpr hRemovedFinite.to_subtype).trans_le
      (Cardinal.aleph0_le_mk W)
  have hRemainingCard : #(↥(removedᶜ)) = #W :=
    Cardinal.mk_compl_of_infinite removed hRemovedSmall
  let indexEquiv : W ≃ ↥(removedᶜ) :=
    (Classical.choice (Cardinal.eq.mp hRemainingCard)).symm
  have hDense :
      ⊤ ≤ (Submodule.span K (Set.range (remainingBasis ∘ indexEquiv))).closure := by
    have hRange : Set.range (remainingBasis ∘ indexEquiv) =
        Set.range remainingBasis := by
      ext vector
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨indexEquiv i, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨indexEquiv.symm j, by simp⟩
    rw [hRange]
    exact remainingBasis.dense_span.ge
  let complementBasis : HilbertBasis W K Mᗮ :=
    HilbertBasis.mk
      (remainingBasis.orthonormal.comp indexEquiv indexEquiv.injective)
      hDense
  let complementUnitary : Mᗮ ≃ₗᵢ[K] H :=
    complementBasis.repr.trans ambientBasis.repr.symm
  let quotientUnitary : (H ⧸ M) ≃ₗᵢ[K] H :=
    M.quotientEquivOrthogonal.trans complementUnitary
  exact ⟨W, complementBasis, ambientBasis,
    complementUnitary, quotientUnitary, rfl, rfl⟩

#print axioms finite_subspace_complement_absorption

end D5.S3.Observer.Completion.FiniteSubspaceComplementAbsorption
