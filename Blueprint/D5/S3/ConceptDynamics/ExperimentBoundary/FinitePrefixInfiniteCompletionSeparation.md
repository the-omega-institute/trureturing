# Finite-Prefix and Infinite-Completion Separation

## Abstract

Every finite prefix of an explicit Bernoulli observation system has equivalent laws, while the completed laws are mutually singular.

**Theorem 1.1 (Finite-prefix laws are equivalent but completions are singular).**

$$\begin{aligned}(\forall m \in \mathbb{N},\\\operatorname{AbsolutelyContinuous}(\operatorname{map}(\operatorname{finiteTranscript}(m), \operatorname{stateLaw}(false)), \operatorname{map}(\operatorname{finiteTranscript}(m), \operatorname{stateLaw}(true))) \land\\\operatorname{AbsolutelyContinuous}(\operatorname{map}(\operatorname{finiteTranscript}(m), \operatorname{stateLaw}(true)), \operatorname{map}(\operatorname{finiteTranscript}(m), \operatorname{stateLaw}(false)))) \land\\\operatorname{MutuallySingular}(\operatorname{stateLaw}(false), \operatorname{stateLaw}(true)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation.finite_prefix_infinite_completion_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation system is the frozen pair of independent Boolean product laws with success probabilities one third and two thirds. Prefixes are obtained by the canonical finiteTranscript map from those same completed laws.

For every finite prefix length, both product laws have full support on the finite Boolean transcript space. Each mapped prefix law is therefore absolutely continuous with respect to the other.

On completed transcripts, the empirical-mean event from the frozen system has probability zero in the lower state and one in the upper state. That same event directly witnesses mutual singularity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation.finite_prefix_infinite_completion_separation`
- Dependency: [D5/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteInexactness](../Experiment/InfiniteIdentificationFiniteInexactness.md)
