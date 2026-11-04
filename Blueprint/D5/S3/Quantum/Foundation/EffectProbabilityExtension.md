# Effect probability extension

## Abstract

Finite additivity on all effects gives a unique density representative.

Let the interface be any finite complex matrix algebra. A single real-valued function on effects is nonnegative, takes value one at the identity, and is additive whenever the sum is an effect. No scalar homogeneity or continuity is assumed. Values outside the effect interval are immaterial.

Equal finite subdivision gives rational homogeneity. Monotonicity and rational approximation give real homogeneity on the unit interval. Scaling each positive matrix into the effect interval defines a positive-cone functional; comparison at a common scale proves independence of scale and additivity.

The positive and negative parts of a Hermitian matrix define its real-linear extension. Equality of two differences is equality of cross sums, which proves well-definedness. Real and imaginary Hermitian parts then give the complex-linear extension. Existing trace-dual positivity represents this functional by a positive matrix. Normalization gives trace one, and the effect span gives uniqueness.

This converse includes dimension two. It supplies the probability representation assumed by the finite-instrument application; neither static event structure nor positive history length implies its probability hypotheses. Busch supplies the mathematical source, while the finite-dimensional construction uses only binary additivity.

**Theorem 1.1 (All complex effects separate matrices).**

Lean statement: `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_trace_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_trace_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two arbitrary finite complex matrices are equal if their trace pairings agree on every positive contraction in the native C-star matrix algebra. The positive contractions span that algebra. Shared-energy pinching consumes this separation after pinching each test effect into the full total-energy commutant.

**Theorem 1.2 (Unique density representation).**

Lean statement: `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_density_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_density_representation` (`✓ std3`). ∎

*Citation.* Paul Busch (2003). *Quantum States and Generalized Observables — A Simple Proof of Gleason’s Theorem*. DOI: [10.1103/PhysRevLett.91.120403](https://doi.org/10.1103/PhysRevLett.91.120403). URL: <https://arxiv.org/html/quant-ph/9909073v3>.

*Commentary.*

Every nonnegative normalized finitely additive probability on all effects is the trace pairing with exactly one positive trace-one matrix. The construction and uniqueness preserve arbitrary finite interface dimension.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_density_representation`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_trace_unique`
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../QuantumChannels/PositiveFilterTransposeRefutation.md)
