# Axis Trace Recurrence

## Abstract

The axis weight is multiplicatively Fibonacci, so consecutive weights compose.

The axis weight reads a depth at both Galois embeddings at once. Its exponent is a linear combination of a golden power and its conjugate, and both powers satisfy the same two-step recurrence, so the exponent is additively Fibonacci and the weight itself is multiplicatively so.

The conjugate step is proved here from its defining quadratic rather than assumed by symmetry: the golden ratio has an upstream power lemma, the conjugate does not, and the two embeddings are not interchangeable in general even though this particular identity holds for both.

**Theorem 1.1 (The axis weight is multiplicatively Fibonacci).**

$$\forall K\in \mathbb{N},\ t_{K+2} = t_{K+1} \cdot t_{K}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisTraceRecurrence.axis_weight_is_multiplicatively_fibonacci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed conjunct is the composition law; the package also carries positivity at every depth and the base value.

## References

- Truth anchor: `D5/S3/Axis/AxisTraceRecurrence.axis_weight_is_multiplicatively_fibonacci`
- Dependency: [D5/S3/Axis/LambdaMinusDirichletSeries](LambdaMinusDirichletSeries.md)
