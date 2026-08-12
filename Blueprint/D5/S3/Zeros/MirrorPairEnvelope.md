# Mirror-Pair Exponential Envelope

## Abstract

A mirror-pair exponential envelope is twice the hyperbolic cosine.

**Theorem 1.1 (The mirror-pair envelope is twice the hyperbolic cosine).**

$$\forall \beta,u\in\mathbb{R},\ \operatorname{exp}((\beta-\frac{1}{2})u) + \operatorname{exp}(-(\beta-\frac{1}{2})u) = 2\operatorname{cosh}((\beta-\frac{1}{2})u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/MirrorPairEnvelope.mirror_pair_envelope_eq_two_cosh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real beta and u, the exponential branch at (beta - 1/2)u plus its reflected branch equals twice the hyperbolic cosine at the same argument. Pinned Mathlib provides Real.cosh_eq, so the Lean proof is a thin wrapper around that identity followed only by ring normalization.

This is a partial closure of the source mirror-pair certificate. The lower bound, strict monotonicity, numerical evaluation, evenness residual, conservation claim, and physical, diffraction, ledger, and concluding interpretations remain unresolved.

## References

- Truth anchor: `D5/S3/Zeros/MirrorPairEnvelope.mirror_pair_envelope_eq_two_cosh`
