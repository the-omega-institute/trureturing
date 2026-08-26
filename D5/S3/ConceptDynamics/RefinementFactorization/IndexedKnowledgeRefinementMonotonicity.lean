/- GID: D5/S3/ConceptDynamics/RefinementFactorization/IndexedKnowledgeRefinementMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/IndexedKnowledgeRefinementMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Indexed readout refinement preserves knowledge, while the converse can fail. -/

import D5.S3.ConceptDynamics.EpistemicRefinement.KnowledgeRefinementMonotonicity

/- Library-search audit trail (2026-08-26):
   * The frozen predecessor states the exact source theorem and its converse
     countermodel, but was withdrawn solely for placement in a new sibling
     bucket. The redo mandate requires a fresh GID without editing that module.
   * The imported family is the single source of truth for `Refines`,
     `jointReadout`, finite-budget monotonicity, and the Boolean countermodel;
     no local carrier, readout, or knowledge predicate is introduced.
   * Pinned Mathlib has no exact epistemic-refinement theorem. The repository
     theorem is applied directly rather than reproved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.IndexedKnowledgeRefinementMonotonicity

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.EpistemicRefinement.KnowledgeRefinementMonotonicity renaming
  knowledge_monotone_under_indexed_refinement_with_converse_countermodel →
    frozen_knowledge_monotonicity

universe u v w z

/-- A target known from a coarse indexed joint readout remains known from every
larger finite budget. One shared Boolean model also shows that fine knowledge
need not descend to the coarser budget. -/
theorem knowledge_monotone_under_indexed_refinement_with_converse_countermodel :
    (∀ {I : Type u} {X : Type v} {O : I -> Type w} {Target : Type z}
        (q : ∀ i, X -> O i) (target : X -> Target)
        {J K : Finset I}, J ⊆ K ->
        Refines target (jointReadout (fun j : J => q j.1)) ->
        Refines target (jointReadout (fun k : K => q k.1))) ∧
      ∃ (q : ∀ _ : Unit, Bool -> Bool) (target : Bool -> Bool)
          (J K : Finset Unit),
        J ⊆ K ∧
          Refines target (jointReadout (fun k : K => q k.1)) ∧
          ¬Refines target (jointReadout (fun j : J => q j.1)) := by
  exact frozen_knowledge_monotonicity

#print axioms knowledge_monotone_under_indexed_refinement_with_converse_countermodel

end D5.S3.ConceptDynamics.RefinementFactorization.IndexedKnowledgeRefinementMonotonicity
