# Refinement-Monotone Safe Coverage

## Abstract

Concept refinement preserves canonical safe answers and monotonically enlarges both their admitted domain and its probability.

**Definition 1.1 (Safe coverage).**

$$\forall X \in Type, B \in Type, Y \in Type, mX \in \operatorname{MeasurableSpace}\left(X\right), P \in \operatorname{ProbabilityMeasure}\left(X\right), A \in X \to Prop, q \in X \to B, T \in X \to Y,\; \operatorname{safeCoverage}\left(P, A, q, T\right) = \operatorname{measure}\left(P, \operatorname{answerDomain}\left(A, q, T\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Answering/RefinementSafeCoverageMonotonicity.safeCoverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Safe coverage is constructed by measuring the canonical admitted safe-answer domain under the supplied probability law.

**Theorem 1.2 (Refinement monotonically enlarges safe coverage).**

$$\forall X \in Type, C \in Type, D \in Type, Y \in Type, mX \in \operatorname{MeasurableSpace}\left(X\right), P \in \operatorname{ProbabilityMeasure}\left(X\right), A \in X \to Prop, qC \in X \to C, qD \in X \to D, T \in X \to Y,\; \operatorname{Refines}\left(qC, qD\right) \Rightarrow \left(\left(\forall x \in X, y \in Y,\; \left(A\left(x\right) \land \operatorname{canonicalSafeAnswer}\left(A, qC, T, qC\left(x\right)\right) = \operatorname{some}\left(y\right)\right) \Rightarrow \operatorname{canonicalSafeAnswer}\left(A, qD, T, qD\left(x\right)\right) = \operatorname{some}\left(y\right)\right) \land \left(\operatorname{answerDomain}\left(A, qC, T\right) \subseteq \operatorname{answerDomain}\left(A, qD, T\right) \land \operatorname{safeCoverage}\left(P, A, qC, T\right) \le \operatorname{safeCoverage}\left(P, A, qD, T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/RefinementSafeCoverageMonotonicity.refinement_safe_coverage_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first public conjunct applies the frozen pointwise theorem: every canonical answer at an admitted state survives refinement with the same target value.

The second conjunct exposes inclusion of admitted answer domains. The third measures that same inclusion under an arbitrary probability law and applies measure monotonicity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/RefinementSafeCoverageMonotonicity.refinement_safe_coverage_monotonicity`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/RefinementSafeCoverageMonotonicity.safeCoverage`
- Dependency: [D5/S3/ConceptDynamics/Answering/RefinementMonotoneAnswerDomain](RefinementMonotoneAnswerDomain.md)
