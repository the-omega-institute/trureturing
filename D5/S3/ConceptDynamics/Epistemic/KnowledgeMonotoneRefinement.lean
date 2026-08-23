/- GID: D5/S3/ConceptDynamics/Epistemic/KnowledgeMonotoneRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Epistemic/KnowledgeMonotoneRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonempty subset of a singleton-answer state retains the same target value. -/

import Mathlib.Data.Set.Card

/- Library-search audit trail (2026-08-23):
   * Repository searches for answer-set knowledge, singleton images, and nonempty subset
     refinement found no theorem with the source conclusion.
   * Existing epistemic modules model evidence-fiber predicates rather than the source's
     set-valued information states, so no sibling knowledge definition is redeclared here.
   * Exact pinned-Mathlib hits `Set.ncard_eq_one` and `Set.image_mono` recover the unique
     source answer and transport image inclusion along the refinement; both are applied
     directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Epistemic.KnowledgeMonotoneRefinement

/-- If a nonempty information state has exactly one attained target value, every nonempty
subset has that same attained target value. -/
theorem knowledge_monotone_under_nonempty_refinement
    {X Y : Type*} (target : X -> Y) (source refined : Set X)
    (refinement : Set.Subset refined source) (refinedNonempty : refined.Nonempty)
    (sourceKnowledge : source.Nonempty /\ (target '' source).ncard = 1) :
    exists value, target '' source = {value} /\ target '' refined = {value} := by
  obtain ⟨value, sourceAnswers⟩ := Set.ncard_eq_one.mp sourceKnowledge.2
  refine ⟨value, sourceAnswers, Set.Subset.antisymm ?_ ?_⟩
  · calc
      target '' refined ⊆ target '' source := Set.image_mono refinement
      _ = {value} := sourceAnswers
  · obtain ⟨state, stateInRefined⟩ := refinedNonempty
    intro answer answerIsValue
    have answerEq : answer = value := Set.mem_singleton_iff.mp answerIsValue
    subst answer
    refine ⟨state, stateInRefined, ?_⟩
    apply Set.mem_singleton_iff.mp
    rw [<- sourceAnswers]
    exact ⟨state, refinement stateInRefined, rfl⟩

/-- A one-state refinement realizes all public hypotheses and preserves its Boolean target. -/
example :
    exists value : Bool,
      (id '' ({true} : Set Bool)) = {value} /\
        (id '' ({true} : Set Bool)) = {value} := by
  apply knowledge_monotone_under_nonempty_refinement
  · exact Set.Subset.rfl
  · exact ⟨true, Set.mem_singleton true⟩
  · exact ⟨⟨true, Set.mem_singleton true⟩, by simp⟩

/-- The nonempty-refinement premise is substantive: the empty subset has no shared
singleton answer with a nonempty singleton source. -/
example :
    Not (exists value : Bool,
      (id '' ({true} : Set Bool)) = {value} /\
        (id '' (∅ : Set Bool)) = {value}) := by
  simp

#print axioms knowledge_monotone_under_nonempty_refinement

end D5.S3.ConceptDynamics.Epistemic.KnowledgeMonotoneRefinement
