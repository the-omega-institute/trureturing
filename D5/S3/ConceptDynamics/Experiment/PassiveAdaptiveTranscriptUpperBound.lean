/- GID: D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Passive adaptive transcripts factor through the complete experiment readout. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-25):
   * Body-shape search for `fun x i => q i x` found the canonical dependent
     product `JointFaithfulnessLeibnizCriterion.jointReadout`, imported below.
   * Searches for passive adaptive protocols, dependent decision trees, and
     transcript factorization found a fixed binary protocol example but no
     general protocol carrier or theorem with this statement.
   * Pinned Mathlib searches for adaptive protocols and transcript
     factorization returned no matching declaration. `loogle` and `leansearch`
     executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- A finite deterministic protocol either stops or selects an experiment and
continues according to the answer returned by that experiment. -/
inductive PassiveProtocol (Experiment : Type u) (Response : Experiment -> Type v) : Type (max u v)
  | stop : PassiveProtocol Experiment Response
  | query (experiment : Experiment)
      (next : Response experiment -> PassiveProtocol Experiment Response) :
      PassiveProtocol Experiment Response

/-- Execute a passive protocol against the supplied experiment channels. The
transcript records each selected experiment together with its actual answer. -/
def runPassiveProtocol {Experiment : Type u} {Response : Experiment -> Type v}
    {State : Type w} (readout : forall experiment, State -> Response experiment) :
    PassiveProtocol Experiment Response -> State -> List (Sigma Response)
  | .stop, _ => []
  | .query experiment next, state =>
      let answer := readout experiment state
      ⟨experiment, answer⟩ :: runPassiveProtocol readout (next answer) state

/-- Replay the same deterministic protocol from the complete tuple of passive
experiment answers. -/
def replayPassiveProtocol {Experiment : Type u} {Response : Experiment -> Type v} :
    PassiveProtocol Experiment Response ->
      (forall experiment, Response experiment) -> List (Sigma Response)
  | .stop, _ => []
  | .query experiment next, answers =>
      let answer := answers experiment
      ⟨experiment, answer⟩ :: replayPassiveProtocol (next answer) answers

/-- Every transcript of a deterministic adaptive protocol using only the
supplied passive experiment family factors through the family's complete joint
readout. -/
theorem passive_adaptive_transcript_upper_bound
    {Experiment : Type u} {Response : Experiment -> Type v} {State : Type w}
    (readout : forall experiment, State -> Response experiment)
    (protocol : PassiveProtocol Experiment Response) :
    Refines (runPassiveProtocol readout protocol) (jointReadout readout) := by
  refine ⟨replayPassiveProtocol protocol, ?_⟩
  funext state
  induction protocol with
  | stop => rfl
  | query experiment next inductionHypothesis =>
      simp only [runPassiveProtocol, Function.comp_apply, replayPassiveProtocol,
        jointReadout]
      exact congrArg
        (List.cons ⟨experiment, readout experiment state⟩)
        (inductionHypothesis (readout experiment state))

#print axioms passive_adaptive_transcript_upper_bound

end D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
