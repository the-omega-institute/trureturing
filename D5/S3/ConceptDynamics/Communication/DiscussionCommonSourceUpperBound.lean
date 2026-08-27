/- GID: D5/S3/ConceptDynamics/Communication/DiscussionCommonSourceUpperBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/DiscussionCommonSourceUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The discussion join remains below its common source. -/

import D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound

/- Library-search audit trail (2026-08-27):
   * Exact D5 hit `indexed_common_source_upper_bound` supplies the atom's first
     clause on the canonical `jointReadout`, but does not expose the clause for
     a source-bounded initial concept joined with the discussion readout.
   * Exact D5 hits `Refines`, `conceptJoin`, and `concept_join_universal` supply
     the canonical factorization order and the required join construction.
   * Repository and pinned Mathlib searches for a theorem exposing both public
     clauses found no exact hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.DiscussionCommonSourceUpperBound

open D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z t

/-- An indexed discussion remains below its common source, and adjoining any
source-bounded initial concept preserves that bound. -/
theorem discussion_common_source_upper_bound
    {Index : Type u} {State : Type v} {Message : Index -> Type w}
    {Source : Type z} (message : forall i, State -> Message i)
    (source : State -> Source)
    (componentBound : forall i, Refines (message i) source) :
    Refines (jointReadout message) source ∧
      forall {Initial : Type t} (initial : State -> Initial),
        Refines initial source ->
          Refines (conceptJoin initial (jointReadout message)) source := by
  have messageBound : Refines (jointReadout message) source :=
    indexed_common_source_upper_bound message source componentBound
  refine ⟨messageBound, ?_⟩
  intro Initial initial initialBound
  exact
    (concept_join_universal initial (jointReadout message) source).2.2
      initialBound messageBound

#print axioms discussion_common_source_upper_bound

end D5.S3.ConceptDynamics.Communication.DiscussionCommonSourceUpperBound
