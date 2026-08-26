# Adaptive Cost and the Passive Boundary

## Abstract

Adaptive protocols can reduce query cost, but passive transcripts remain bounded by the complete joint experiment readout.

**Theorem 1.1 (Adaptivity cannot cross the complete passive boundary).**

$$\begin{aligned}\forall U, X, Y: \operatorname{Type}, R: U \to \operatorname{Type},\\q: \forall u: U, X \to R_{u}, T: X \to Y,\\\neg\operatorname{Refines}\left(T, \operatorname{jointReadout}\left(q\right)\right) \implies \\D_{ad} < D_{stat} \land \neg\exists pi: \operatorname{PassiveProtocol}\left(U, R\right), \operatorname{Refines}\left(T, \operatorname{runPassiveProtocol}\left(q, pi\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentBoundary/PassiveJointBoundaryObstruction.adaptive_cost_reduction_and_passive_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The modular four-state witness has minimum adaptive depth two and minimum fixed-suite cardinality three, so adaptive selection can strictly lower experiment cost.

For an arbitrary passive experiment family, every deterministic adaptive transcript is replayable from the complete dependent tuple of experiment answers. Any recovery from the transcript would therefore recover the target from that complete tuple.

The quantified protocol class keeps the experiment family, state carrier, response carriers, readout channels, and admitted domain fixed. A successful scheme beyond this boundary must leave that class through new experiments, a changed object, intervention, expanded observations, or an added domain premise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/PassiveJointBoundaryObstruction.adaptive_cost_reduction_and_passive_boundary`
- Dependency: [D5/S3/ConceptDynamics/Coding/AdaptiveResidueIdentification](../Coding/AdaptiveResidueIdentification.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound](../Experiment/PassiveAdaptiveTranscriptUpperBound.md)
