/- GID: D5/S3/ConceptDynamics/ExperimentBoundary/PassiveJointBoundaryObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentBoundary/PassiveJointBoundaryObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adaptivity can lower query cost but cannot identify beyond the passive readout. -/

import D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

/- Library-search audit trail (2026-08-26):
   * Exact current-tree hits `PassiveProtocol`, `runPassiveProtocol`, and
     `passive_adaptive_transcript_upper_bound` supply the source's finite
     passive decision trees, transcript, and joint-readout factorization.
   * Body-shape searches for `fun state experiment => readout experiment state`
     and dependent readout products found the canonical `jointReadout`, which
     is imported rather than redeclared.
   * Exact current-tree hit `two_step_adaptive_residue_identification` supplies
     the source's possibility clause: an explicitly constructed adaptive
     protocol has cost two while every exact fixed suite has cost three.
   * Repository and pinned-Mathlib searches found no theorem already combining
     the cost witness with the general passive-boundary obstruction. `loogle`
     and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentBoundary.PassiveJointBoundaryObstruction

open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- The explicit modular model shows that adaptivity can strictly reduce query
cost. In general, however, if a target does not factor through the complete
joint readout of a passive experiment family, then no deterministic adaptive
protocol using only that family can identify the target exactly. Such a scheme
must leave this fixed passive setting by changing its experiments, state,
intervention behavior, observation carrier, or admitted domain. -/
theorem adaptive_cost_reduction_and_passive_boundary
    {Experiment : Type u} {Response : Experiment -> Type v}
    {State : Type w} {Target : Type z}
    (readout : forall experiment, State -> Response experiment)
    (target : Concept State Target)
    (notRefines : ¬Refines target (jointReadout readout)) :
    residueAdaptiveDepth < residueStaticDepth ∧
      ¬ ∃ protocol : PassiveProtocol Experiment Response,
        Refines target (runPassiveProtocol readout protocol) := by
  constructor
  · exact two_step_adaptive_residue_identification.2.2.2.2.2.2.2
  · rintro ⟨protocol, recovery, targetFromTranscript⟩
    rcases passive_adaptive_transcript_upper_bound readout protocol with
      ⟨replay, transcriptFromJoint⟩
    apply notRefines
    refine ⟨recovery ∘ replay, ?_⟩
    rw [targetFromTranscript, transcriptFromJoint]
    rfl

#print axioms adaptive_cost_reduction_and_passive_boundary

end D5.S3.ConceptDynamics.ExperimentBoundary.PassiveJointBoundaryObstruction
