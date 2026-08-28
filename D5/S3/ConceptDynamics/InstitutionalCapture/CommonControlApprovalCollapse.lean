/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/CommonControlApprovalCollapse
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/CommonControlApprovalCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint approvals and their final judgment remain below a common control source. -/

import D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound

/- Library-search audit trail (2026-08-26):
   * Exact D5 clause hit `indexed_common_source_upper_bound` supplies the
     canonical dependent joint approval readout and its common-source factor.
   * `common_source_capture_number_eq_one` concerns a different minimum over
     controlled source sets and is not a whole-statement match.
   * Searches of D5 and pinned Mathlib found no exact theorem that also carries
     an arbitrary final authorization map through the selected joint factor.
     The proof uses only that imported factor and ordinary function composition.
   * No new source, approval, joint-readout, or factorization primitive is
     introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.CommonControlApprovalCollapse

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Communication.IndexedCommonSourceUpperBound

/-- If every approval node is a postprocessing of one control source, their
canonical joint readout is still a postprocessing of that source, and every
final judgment computed from the joint approvals factors through it as well. -/
theorem common_control_source_approval_collapse
    {Index State Source Judgment : Type*} {Approval : Index -> Type*}
    (approval : forall i, State -> Approval i)
    (source : State -> Source)
    (finalize : (forall i, Approval i) -> Judgment)
    (componentBound : forall i, Refines (approval i) source) :
    Refines (jointReadout approval) source /\
      exists g : Source -> Judgment,
        finalize ∘ jointReadout approval = g ∘ source := by
  rcases indexed_common_source_upper_bound approval source componentBound with
    ⟨assemble, jointFactorization⟩
  constructor
  · exact ⟨assemble, jointFactorization⟩
  · refine ⟨finalize ∘ assemble, ?_⟩
    rw [jointFactorization]
    rfl

#print axioms common_control_source_approval_collapse

end D5.S3.ConceptDynamics.InstitutionalCapture.CommonControlApprovalCollapse
