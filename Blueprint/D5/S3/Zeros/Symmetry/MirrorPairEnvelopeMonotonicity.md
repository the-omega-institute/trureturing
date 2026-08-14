# Mirror-Pair Envelope Monotonicity

## Abstract

A positive-slope mirror-pair envelope is strictly increasing on nonnegative inputs.

**Theorem 1.1 (The positive-slope mirror-pair envelope is strictly increasing).**

$$\forall \beta\in\mathbb{R},\ \beta>\frac{1}{2} \Rightarrow \forall u,v\in[0,\infty),\ u<v \Rightarrow \operatorname{exp}((\beta-\frac{1}{2})u) + \operatorname{exp}(-(\beta-\frac{1}{2})u) < \operatorname{exp}((\beta-\frac{1}{2})v) + \operatorname{exp}(-(\beta-\frac{1}{2})v).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/MirrorPairEnvelopeMonotonicity.mirror_pair_envelope_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For beta greater than one half, the slope beta - 1/2 is positive. Multiplication by that slope preserves the order of nonnegative inputs, and the frozen envelope identity rewrites both sides as twice the hyperbolic cosine. Mathlib's strict monotonicity theorem for cosh on nonnegative arguments then proves the displayed strict inequality.

This is a continuation of the earlier envelope identity and closes only the strict-monotonicity clause. The stated numerical value near 3.62, its numerical certificate, and the semantic conservation and zero-pair interpretations remain unresolved.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/MirrorPairEnvelopeMonotonicity.mirror_pair_envelope_strictMonoOn`
- Dependency: [D5/S3/Zeros/MirrorPairEnvelope](../MirrorPairEnvelope.md)
