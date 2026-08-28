/- GID: D5/S3/ConceptDynamics/Discussion/BoundedDiscussionBlindSpotPersistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Discussion/BoundedDiscussionBlindSpotPersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Messages bounded by a joint interface cannot remove its target blind spot. -/

import D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound
import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-26):
   * Exact D5 primitive hit `jointReadout` is the canonical dependent join of
     an indexed message family; the body-shape search `fun x i => q i x`
     located it before this module was authored.
   * Exact D5 theorem `indexed_common_source_upper_bound` proves that the joint
     message readout factors through a common source when every message does.
   * Exact D5 hits `concept_join_universal` and `refinement_transitive` supply
     the remaining join bound and contradiction. No existing theorem packages
     the target blind-spot conclusion with the indexed-message premise.
   * Pinned Mathlib has generic `Function.FactorsThrough` extension and
     composition support, but the frozen D5 `Refines` relation and canonical
     readout constructors are the source-family single source of truth. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Discussion.BoundedDiscussionBlindSpotPersistence

open D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- If the target is not determined by the two agents' joint interface and
every discussion message factors through that same interface, then adjoining
the entire indexed message family still does not determine the target. -/
theorem bounded_discussion_cannot_remove_joint_blind_spot
    {Index State LeftValue RightValue TargetValue : Type*}
    {MessageValue : Index -> Type*}
    (left : State -> LeftValue) (right : State -> RightValue)
    (message : forall index, State -> MessageValue index)
    (target : State -> TargetValue)
    (initialBlindSpot :
      ¬Refines (canonicalTargetReadout target) (conceptJoin left right))
    (messageBound :
      forall index, Refines (message index) (conceptJoin left right)) :
    ¬Refines (canonicalTargetReadout target)
      (conceptJoin (conceptJoin left right) (jointReadout message)) := by
  intro targetResolved
  have jointMessageBound :
      Refines (jointReadout message) (conceptJoin left right) :=
    indexed_common_source_upper_bound message (conceptJoin left right) messageBound
  have extendedDiscussionBound :
      Refines (conceptJoin (conceptJoin left right) (jointReadout message))
        (conceptJoin left right) :=
    (concept_join_universal (conceptJoin left right) (jointReadout message)
      (conceptJoin left right)).2.2 ⟨id, rfl⟩ jointMessageBound
  exact initialBlindSpot
    (refinement_transitive (canonicalTargetReadout target)
      (conceptJoin (conceptJoin left right) (jointReadout message))
      (conceptJoin left right) extendedDiscussionBound targetResolved)

#print axioms bounded_discussion_cannot_remove_joint_blind_spot

end D5.S3.ConceptDynamics.Discussion.BoundedDiscussionBlindSpotPersistence
