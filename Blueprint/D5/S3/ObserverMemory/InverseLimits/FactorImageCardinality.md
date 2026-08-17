# Factor Image Cardinality

## Abstract

A surjective factor map carries every finite iterate image onto the factor image.

**Theorem 1.1 (Factor iterate images have no larger cardinality).**

$$\forall Y, Z,\ [\operatorname{Fintype} Y] [\operatorname{Fintype} Z],\ phi: Y \to Z, tau: Y \to Y, sigma: Z \to Z, \operatorname{Surjective}\left(phi\right) \land \operatorname{Semiconj}\left(phi, tau, sigma\right) \Rightarrow\ \forall k\in \mathbb{N},\ \operatorname{image}(phi, \operatorname{range}(tau^{k})) = \operatorname{range}(sigma^{k}) \land \operatorname{ncard}(\operatorname{range}(sigma^{k})) \leq \operatorname{ncard}(\operatorname{range}(tau^{k})).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/FactorImageCardinality.factor_iterate_range_image_and_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y and Z be finite carriers, tau and sigma self-maps, and phi a surjective map with phi semiconjugating tau to sigma. For every iterate k, phi maps the range of tau^k exactly onto the range of sigma^k. The finite cardinality of the factor image is therefore at most that of the original image.

Pinned Mathlib supplies Function.Semiconj.iterate_right for the iterated semiconjugacy and Set.ncard_image_le for the exact finite image bound. The proof uses the surjectivity hypothesis only for the reverse inclusion in the image equality.

This closes the image-equality and cardinality clauses of qdo-v1 theorem 8.6. It does not claim the separate assertion that a stable source image chain forces a stable factor chain.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/FactorImageCardinality.factor_iterate_range_image_and_cardinality`
