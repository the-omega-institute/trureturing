/- GID: D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The joint message readout remains bounded by every message's common source. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-25):
   * Exact D5 hits `ConceptJoinUniversal.Refines` and
     `JointFaithfulnessLeibnizCriterion.jointReadout` are imported as the
     factorization order and canonical indexed join.
   * `IndexedReadoutMonotonicity` treats restriction from a larger finite family,
     not factorization of an arbitrary indexed family through one common source.
   * Repository and pinned Mathlib searches for indexed common-source
     factorization found no full-statement theorem. `loogle` and `leansearch`
     executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- If every message readout factors through one common source readout, their
canonical joint readout factors through that same source. -/
theorem indexed_common_source_upper_bound
    {Index : Type u} {State : Type v} {Message : Index -> Type w}
    {Source : Type z} (message : forall i, State -> Message i)
    (source : State -> Source)
    (componentBound : forall i, Refines (message i) source) :
    Refines (jointReadout message) source := by
  choose factor factorization using componentBound
  refine ⟨fun sourceValue i => factor i sourceValue, ?_⟩
  funext state i
  exact congrFun (factorization i) state

#print axioms indexed_common_source_upper_bound

end D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound
