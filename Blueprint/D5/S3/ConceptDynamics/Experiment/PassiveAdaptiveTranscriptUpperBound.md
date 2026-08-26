# Passive Adaptive Transcript Upper Bound

## Abstract

Every deterministic adaptive transcript using a passive experiment family factors through the complete joint experiment readout.

**Theorem 1.1 (Every passive adaptive transcript factors through all experiment answers).**

$$\begin{aligned}\forall U, X: \operatorname{Type}, R: U \to \operatorname{Type},\\q: \forall u: U, X \to R_{u},\\pi: \operatorname{PassiveProtocol}\left(U, R\right), \operatorname{Refines}\left(\operatorname{runPassiveProtocol}\left(q, pi\right), \operatorname{jointReadout}\left(q\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.passive_adaptive_transcript_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A passive protocol is a finite dependent decision tree. At each query node, the answer selects the continuation, so later experiments may depend on the transcript already observed.

The operational evaluator reads each selected channel from the state. A separate replay evaluator follows the same tree from the complete dependent tuple of all experiment answers. Induction on the protocol identifies the two transcripts and supplies the factor map.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.passive_adaptive_transcript_upper_bound`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
