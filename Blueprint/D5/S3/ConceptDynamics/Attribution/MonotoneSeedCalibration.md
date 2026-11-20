# Positive-mass witnesses for nested events

## Abstract

Strict increases in the mass of nested events require distinct positive-mass seeds.

**Theorem 1.1 (Distinct positive-mass seeds for successive increases).**

$$\forall m E w, \operatorname{MonotoneOn}\left(E, \operatorname{Iic}\left(m\right)\right) \land \operatorname{StrictMonoOn}\left(\operatorname{Mass}\left(E, w\right), \operatorname{Iic}\left(m\right)\right) \Rightarrow \exists i: \operatorname{Embedding}\left(\operatorname{Fin}\left(m\right), \{s \mid 0 < \operatorname{w}\left(s\right)\}\right), \forall k: \operatorname{Fin}\left(m\right), \operatorname{i}\left(k\right) \in \operatorname{E}\left(k + 1\right) \land \neg(\operatorname{i}\left(k\right) \in \operatorname{E}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/MonotoneSeedCalibration.positive_seed_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the finite events from index 0 through m be nested and have strictly increasing total real weight. There is an embedding from Fin m into the positive-weight seeds. The image of each index belongs to the next event and not to its current event.

The weight of each difference equals the increase in event weight. A positive sum gives a positive term. The differences are disjoint because each earlier event is contained in the event subtracted from every later increment.

For exact masses k/m on the binary grid, at least m positive-weight seeds are needed. Uniform seeds numbered from 0 to m minus 1 attain the bound by choosing label 1 when the seed index is below k. Reflecting the seed and reversing the probability index complements this event and preserves the uniform law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/MonotoneSeedCalibration.positive_seed_embedding`
