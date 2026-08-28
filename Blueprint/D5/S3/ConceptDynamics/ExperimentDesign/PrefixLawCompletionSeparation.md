# Prefix-Law and Completion Separation

## Abstract

Every finite prefix of an explicit Bernoulli observation system has equivalent laws, while the completed laws are mutually singular.

**Theorem 1.1 (Finite-prefix laws are equivalent but completions are singular).**

$$\begin{aligned}(\forall m \in \mathbb{N},\\\operatorname{AbsolutelyContinuous}(\operatorname{map}(\operatorname{finiteTranscript}(m), \operatorname{stateLaw}(false)), \operatorname{map}(\operatorname{finiteTranscript}(m), \operatorname{stateLaw}(true))) \land\\\operatorname{AbsolutelyContinuous}(\operatorname{map}(\operatorname{finiteTranscript}(m), \operatorname{stateLaw}(true)), \operatorname{map}(\operatorname{finiteTranscript}(m), \operatorname{stateLaw}(false)))) \land\\\operatorname{MutuallySingular}(\operatorname{stateLaw}(false), \operatorname{stateLaw}(true)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/PrefixLawCompletionSeparation.finite_prefix_infinite_completion_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation system is the canonical pair of independent Boolean product laws with success probabilities one third and two thirds. Prefixes use finiteTranscript on those same completed laws.

For every finite prefix length, each mapped law is absolutely continuous with respect to the other.

The canonical empirical-mean event separates the two completed laws and therefore witnesses their mutual singularity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/PrefixLawCompletionSeparation.finite_prefix_infinite_completion_separation`
- Dependency: [D5/S3/ConceptDynamics/ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation](../ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation.md)
