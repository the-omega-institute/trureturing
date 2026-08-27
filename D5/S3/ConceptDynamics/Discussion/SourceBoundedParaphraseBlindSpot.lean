/- GID: D5/S3/ConceptDynamics/Discussion/SourceBoundedParaphraseBlindSpot
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Discussion/SourceBoundedParaphraseBlindSpot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Any indexed family of source-bounded paraphrases preserves a target blind spot. -/

import D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound
import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-27):
   * Exact D5 primitive hit `jointReadout` is the canonical dependent readout of
     an indexed paraphrase family; the body-shape search `fun x i => q i x`
     located it before this module was authored.
   * Exact D5 theorem `indexed_common_source_upper_bound` proves that every
     source-bounded family has a source-bounded joint readout.
   * Exact D5 theorem `refinement_transitive` transports a hypothetical target
     resolution through that bound to contradict the public source blind spot.
   * `bounded_discussion_cannot_remove_joint_blind_spot` fixes the source to a
     two-readout join and therefore is not an exact arbitrary-source hit.
     Pinned Mathlib has no theorem on the D5 refinement carrier and canonical
     joint readout; `loogle` and `leansearch` were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Discussion.SourceBoundedParaphraseBlindSpot

open D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

universe u v w z t

/-- If the target is not determined by a source and every paraphrase factors
through that source, then their complete indexed joint readout still does not
determine the target. -/
theorem source_bounded_paraphrases_preserve_target_blind_spot
    {Index : Type u} {State : Type v} {Message : Index -> Type w}
    {Source : Type z} {Target : Type t}
    (paraphrase : forall index, State -> Message index)
    (source : State -> Source) (target : State -> Target)
    (sourceBlindSpot : ¬Refines (canonicalTargetReadout target) source)
    (paraphraseBound : forall index, Refines (paraphrase index) source) :
    ¬Refines (canonicalTargetReadout target) (jointReadout paraphrase) := by
  intro targetResolved
  have jointParaphraseBound : Refines (jointReadout paraphrase) source :=
    indexed_common_source_upper_bound paraphrase source paraphraseBound
  exact sourceBlindSpot
    (refinement_transitive (canonicalTargetReadout target)
      (jointReadout paraphrase) source jointParaphraseBound targetResolved)

#print axioms source_bounded_paraphrases_preserve_target_blind_spot

end D5.S3.ConceptDynamics.Discussion.SourceBoundedParaphraseBlindSpot
