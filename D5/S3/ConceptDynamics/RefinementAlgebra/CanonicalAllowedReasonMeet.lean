/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/CanonicalAllowedReasonMeet
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/CanonicalAllowedReasonMeet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Meet closure gives a canonical unique coarsest allowed sufficient reason. -/

import D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

/- Library-search audit trail (2026-08-27):
   * Exact repository hits `ConceptClass`, `conceptKernelOrderIso`, and
     `Setoid.completeLattice` provide the canonical concept-class carrier and
     its order-dual equivalence-relation lattice; they are imported and used
     directly, with no duplicate concept or refinement definition.
   * `PermissionIntersectionLeast.sufficient_intersection_is_unique_least` is
     an adjacent theorem about subsets ordered by inclusion. It does not expose
     the source concept carrier, allowed doctrine, target sufficiency, or the
     transported concept meet, so it is not an exact hit.
   * Pinned Mathlib exact supporting hits `le_sInf`, `sInf_le`, and
     `IsLeast.unique` supply the complete-lattice and uniqueness steps. Searches
     for an existing theorem combining the allowed doctrine, target lower bound,
     transported meet, closure premise, and unique least element found no hit.
   * Body-shape searches for an allowed set of setoids/concept classes and an
     infimum transported through `conceptKernelOrderIso` found no existing D5
     primitive. No new `def` or `abbrev` is introduced here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.CanonicalAllowedReasonMeet

open D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

universe u

/-- If an allowed doctrine contains a sufficient concept and contains the
canonical meet whenever that sufficient family is nonempty, the transported
concept meet is the least acceptable reason and that least reason is unique. -/
theorem meet_closed_allowed_reasons_have_unique_coarsest_ratio
    {X : Type u}
    (allowed : Set (ConceptClass X))
    (judgmentEssence : ConceptClass X)
    (hExists :
      {reason : ConceptClass X |
        reason ∈ allowed ∧ judgmentEssence ≤ reason}.Nonempty)
    (hMeetClosed :
      {reason : ConceptClass X |
          reason ∈ allowed ∧ judgmentEssence ≤ reason}.Nonempty →
        (conceptKernelOrderIso X).symm
            (sInf ((conceptKernelOrderIso X) ''
              {reason : ConceptClass X |
                reason ∈ allowed ∧ judgmentEssence ≤ reason})) ∈ allowed) :
    IsLeast
        {reason : ConceptClass X |
          reason ∈ allowed ∧ judgmentEssence ≤ reason}
        ((conceptKernelOrderIso X).symm
          (sInf ((conceptKernelOrderIso X) ''
            {reason : ConceptClass X |
              reason ∈ allowed ∧ judgmentEssence ≤ reason}))) ∧
      ∃! reason : ConceptClass X,
        IsLeast
          {candidate : ConceptClass X |
            candidate ∈ allowed ∧ judgmentEssence ≤ candidate}
          reason := by
  let acceptable : Set (ConceptClass X) :=
    {reason | reason ∈ allowed ∧ judgmentEssence ≤ reason}
  let ratio : ConceptClass X :=
    (conceptKernelOrderIso X).symm
      (sInf ((conceptKernelOrderIso X) '' acceptable))
  have ratioAllowed : ratio ∈ allowed := by
    simpa only [acceptable, ratio] using hMeetClosed hExists
  have judgmentBelowRatio : judgmentEssence ≤ ratio := by
    have mapped :
        conceptKernelOrderIso X judgmentEssence ≤
          sInf ((conceptKernelOrderIso X) '' acceptable) := by
      apply le_sInf
      intro encoded encodedInImage
      obtain ⟨reason, reasonAcceptable, rfl⟩ := encodedInImage
      exact (conceptKernelOrderIso X).monotone reasonAcceptable.2
    have transported := (conceptKernelOrderIso X).symm.monotone mapped
    simpa only [OrderIso.symm_apply_apply, ratio] using transported
  have ratioBelowEvery : ∀ reason ∈ acceptable, ratio ≤ reason := by
    intro reason reasonAcceptable
    have mapped :
        sInf ((conceptKernelOrderIso X) '' acceptable) ≤
          conceptKernelOrderIso X reason :=
      sInf_le ⟨reason, reasonAcceptable, rfl⟩
    have transported := (conceptKernelOrderIso X).symm.monotone mapped
    simpa only [OrderIso.symm_apply_apply, ratio] using transported
  have ratioLeast : IsLeast acceptable ratio :=
    ⟨⟨ratioAllowed, judgmentBelowRatio⟩, ratioBelowEvery⟩
  refine ⟨ratioLeast, ratio, ratioLeast, ?_⟩
  intro reason reasonLeast
  exact reasonLeast.unique ratioLeast

example :
    let judgmentEssence : ConceptClass Bool :=
      toAntisymmetrization
        (fun left right : EffectiveConcept Bool => left ≤ right)
        (relationConcept (⊤ : Setoid Bool))
    let allowed : Set (ConceptClass Bool) := Set.univ
    IsLeast
        {reason : ConceptClass Bool |
          reason ∈ allowed ∧ judgmentEssence ≤ reason}
        ((conceptKernelOrderIso Bool).symm
          (sInf ((conceptKernelOrderIso Bool) ''
            {reason : ConceptClass Bool |
              reason ∈ allowed ∧ judgmentEssence ≤ reason}))) ∧
      ∃! reason : ConceptClass Bool,
        IsLeast
          {candidate : ConceptClass Bool |
            candidate ∈ allowed ∧ judgmentEssence ≤ candidate}
          reason := by
  dsimp only
  apply meet_closed_allowed_reasons_have_unique_coarsest_ratio
  · exact ⟨_, Set.mem_univ _, le_rfl⟩
  · intro _
    exact Set.mem_univ _

#print axioms meet_closed_allowed_reasons_have_unique_coarsest_ratio

end D5.S3.ConceptDynamics.RefinementAlgebra.CanonicalAllowedReasonMeet
