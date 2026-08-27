/- GID: D5/S3/ConceptDynamics/Discussion/CommonSourceEchoLimit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Discussion/CommonSourceEchoLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Common-source message repetition cannot resolve a target blind to that source. -/

import D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound
import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-27):
   * The body-shape search `fun x i => q i x` found the canonical dependent
     product `jointReadout`, which is imported rather than redeclared.
   * Exact D5 hits `Refines`, `canonicalTargetReadout`,
     `indexed_common_source_upper_bound`, and `refinement_transitive` supply the
     source semantics and both factorization steps directly.
   * `bounded_discussion_cannot_remove_joint_blind_spot` is restricted to a
     two-readout joint source and exposes only blind-spot persistence, not the
     necessary out-of-source-message clause. No full-statement D5 hit exists.
   * Pinned Mathlib contains the classical `not_forall` family, but no exact
     common-source target-blindness theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Discussion.CommonSourceEchoLimit

open D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- Repeating or jointly collecting messages that all factor through one source
cannot resolve a target blind to that source. Conversely, any resolving message
family must contain a message that does not factor through the common source. -/
theorem common_source_repetition_cannot_resolve_blind_target
    {Index State Source TargetValue : Type*}
    {MessageValue : Index -> Type*}
    (source : State -> Source)
    (message : forall index, State -> MessageValue index)
    (target : State -> TargetValue)
    (targetBlind :
      ¬Refines (canonicalTargetReadout target) source) :
    ((forall index, Refines (message index) source) ->
      ¬Refines (canonicalTargetReadout target) (jointReadout message)) ∧
    (Refines (canonicalTargetReadout target) (jointReadout message) ->
      ∃ index, ¬Refines (message index) source) := by
  constructor
  · intro componentBound targetResolved
    have jointBound : Refines (jointReadout message) source :=
      indexed_common_source_upper_bound message source componentBound
    exact targetBlind
      (refinement_transitive (canonicalTargetReadout target)
        (jointReadout message) source jointBound targetResolved)
  · intro targetResolved
    classical
    by_contra noOutsideMessage
    have componentBound : forall index, Refines (message index) source := by
      intro index
      by_contra notBound
      exact noOutsideMessage ⟨index, notBound⟩
    have jointBound : Refines (jointReadout message) source :=
      indexed_common_source_upper_bound message source componentBound
    exact targetBlind
      (refinement_transitive (canonicalTargetReadout target)
        (jointReadout message) source jointBound targetResolved)

#print axioms common_source_repetition_cannot_resolve_blind_target

end D5.S3.ConceptDynamics.Discussion.CommonSourceEchoLimit
