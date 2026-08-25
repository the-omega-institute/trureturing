/- GID: D5/S3/ConceptDynamics/Refinement/SemanticResourceSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/SemanticResourceSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: More semantic targets than allowed algorithms force a resource-unreachable target. -/

import D5.S3.ConceptDynamics.Refinement.ResourceRefinementComposition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

/- Library-search audit trail (2026-08-22):
   * Repository searches found no theorem separating semantic factorization from
     resource factorization by counting a finite allowed algorithm class.
   * Exact family hits `Concept`, `Refines`, `ResourceCost`, and `ResourceRefines`
     are imported and used directly; no sibling refinement predicate is declared.
   * Pinned Mathlib's exact `Fintype.card_fun`, `Finset.card_image_le`, and
     `Finset.card_lt_iff_ne_univ` results give the function count, restriction-image
     bound, and missing function. They are applied directly below.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.SemanticResourceSeparation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.ResourceRefinementComposition

universe u

/-- If the number of targets on the finite image of a concept exceeds the
number of budget-admissible algorithms, some target factors semantically
through the concept but has no factor within the resource budget. -/
theorem semantic_sufficiency_can_exceed_finite_resources
    {X B Y : Type u} [Fintype Y] [Nonempty Y]
    (readout : Concept X B) [Fintype (Set.range readout)]
    (cost : ResourceCost) (budget : Nat)
    (allowed : Finset (B -> Y))
    (allowed_iff_budget : forall factor : B -> Y,
      factor ∈ allowed <-> cost factor <= budget)
    (more_targets :
      allowed.card < Fintype.card Y ^ Fintype.card (Set.range readout)) :
    exists target : Concept X Y,
      Refines target readout /\
        Not (ResourceRefines cost budget target readout) := by
  classical
  let restrict : (B -> Y) -> (Set.range readout -> Y) :=
    fun factor value => factor value.1
  let allowedRestrictions : Finset (Set.range readout -> Y) :=
    allowed.image restrict
  have restriction_card_le : allowedRestrictions.card <= allowed.card := by
    exact Finset.card_image_le
  have restriction_card_lt :
      allowedRestrictions.card < Fintype.card (Set.range readout -> Y) := by
    rw [Fintype.card_fun]
    exact restriction_card_le.trans_lt more_targets
  have restrictions_ne_univ : Ne allowedRestrictions Finset.univ :=
    (Finset.card_lt_iff_ne_univ allowedRestrictions).mp restriction_card_lt
  obtain ⟨missing, missing_not_allowed⟩ :
      exists factor : Set.range readout -> Y,
        factor ∉ allowedRestrictions := by
    by_contra no_missing
    apply restrictions_ne_univ
    apply Finset.eq_univ_iff_forall.mpr
    intro factor
    by_contra factor_not_allowed
    exact no_missing ⟨factor, factor_not_allowed⟩
  let target : Concept X Y :=
    fun state => missing ⟨readout state, Set.mem_range_self state⟩
  let fallback : Y := Classical.choice inferInstance
  let extension : B -> Y := fun value =>
    if in_range : value ∈ Set.range readout
    then missing ⟨value, in_range⟩
    else fallback
  refine ⟨target, ?_, ?_⟩
  · refine ⟨extension, ?_⟩
    funext state
    change missing ⟨readout state, Set.mem_range_self state⟩ =
      (if in_range : ∃ source, readout source = readout state
        then missing ⟨readout state, in_range⟩ else fallback)
    rw [dif_pos ⟨state, rfl⟩]
  · rintro ⟨factor, factorizes, within_budget⟩
    apply missing_not_allowed
    apply Finset.mem_image.mpr
    refine ⟨factor, (allowed_iff_budget factor).mpr within_budget, ?_⟩
    funext value
    rcases value with ⟨_, ⟨state, rfl⟩⟩
    change factor (readout state) = target state
    have hfactorAt := congrFun factorizes state
    change target state = factor (readout state) at hfactorAt
    exact hfactorAt.symm

#print axioms semantic_sufficiency_can_exceed_finite_resources

end D5.S3.ConceptDynamics.Refinement.SemanticResourceSeparation
