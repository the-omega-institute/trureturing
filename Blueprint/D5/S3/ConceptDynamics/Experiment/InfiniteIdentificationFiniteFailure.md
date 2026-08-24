# Infinite Identification without Finite Exact Tomography

## Abstract

A countable transcript can identify two probability laws almost surely even though their coordinate laws are equivalent and no finite prefix admits an exact decoder.

**Theorem 1.1 (Almost-sure infinite identification has no finite exact converse).**

$$\begin{aligned}\operatorname{AC}\left(\operatorname{marginal}\left(lowerBias\right), \operatorname{marginal}\left(upperBias\right)\right) \land\\\operatorname{AC}\left(\operatorname{marginal}\left(upperBias\right), \operatorname{marginal}\left(lowerBias\right)\right) \land\\\operatorname{Measurable}\left(distinguishingEvent\right) \land\\\operatorname{Pr}\left(\operatorname{stateLaw}\left(false\right), distinguishingEvent\right) = 0 \land\\\operatorname{Pr}\left(\operatorname{stateLaw}\left(true\right), distinguishingEvent\right) = 1 \land\\\neg \exists m: \operatorname{Nat}, d: (\operatorname{Fin}\left(m\right) \to \operatorname{Bool}) \to \operatorname{Bool}, \operatorname{AE}\left(\operatorname{stateLaw}\left(false\right), \lambda x \mapsto \operatorname{d}\left(\operatorname{finiteTranscript}\left(m, x\right)\right) = false\right) \land \operatorname{AE}\left(\operatorname{stateLaw}\left(true\right), \lambda x \mapsto \operatorname{d}\left(\operatorname{finiteTranscript}\left(m, x\right)\right) = true\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteFailure.infinite_identification_not_finite_exact_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two states generate independent Boolean product laws with constant success probabilities one third and two thirds. Both Boolean coordinate laws have full support, hence are mutually absolutely continuous.

The measurable classifier event consists of transcripts whose empirical means converge to two thirds. The strong law gives probability zero for this event in the lower state and probability one in the upper state.

At every finite prefix length, the all-false cylinder has positive mass under both product laws. A decoder that is almost surely correct would therefore have to label that same prefix both false and true.

Pinned Mathlib supplies Bernoulli laws, product-coordinate independence, the strong law, and convergence-event measurability. The repository's canonical varying-marginal green-class theorem supplies finite-cylinder positivity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteFailure.infinite_identification_not_finite_exact_tomography`
- Dependency: [D5/S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure](../../../S0/Asymptotics/MetricGeometry/VaryingMarginalGreenClassMeasure.md)
