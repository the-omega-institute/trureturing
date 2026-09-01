# Finite Protocol Compression

## Abstract

A finite protocol quotient has an exact certificate with at most one fewer protocols than classes.

**Theorem 1.1 (Finite quotients admit sharp protocol certificates).**

$$\begin{aligned}\forall Protocol, State, Observation: \operatorname{Type},\\{}[\operatorname{Finite} State], Q: \operatorname{Set}(Protocol), e: Protocol \to State \to Observation,\\{}\exists Q0: \operatorname{Finset}(Protocol),\\{}\operatorname{subset}(Q0, Q) \land\\{}\operatorname{experimentIndistinguishability}(Q0, e) = \operatorname{experimentIndistinguishability}(Q, e) \land\\{}\operatorname{card}(Q0) \leq \operatorname{card}(\operatorname{ProtocolQuotient}(Q, e)) - 1.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProtocolEvaluation/FiniteProtocolCompression.finite_protocol_subfamily_card_le_quotient_card_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state carrier, let K(Q) be equality of all evaluation readouts indexed by the available protocol family Q. The quotient is the actual quotient of the state carrier by this kernel.

There is a finite selected protocol family contained in Q whose kernel equals K(Q), and its cardinality is at most the number of quotient classes minus one.

## References

- Truth anchor: `D5/S3/Observer/ProtocolEvaluation/FiniteProtocolCompression.finite_protocol_subfamily_card_le_quotient_card_sub_one`
- Dependency: [D5/S3/ConceptDynamics/Experiment/ExperimentExpansionMonotonicity](../../ConceptDynamics/Experiment/ExperimentExpansionMonotonicity.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/StrictRefinementBound](../../ConceptDynamics/Refinement/StrictRefinementBound.md)
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate](../../ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate.md)
