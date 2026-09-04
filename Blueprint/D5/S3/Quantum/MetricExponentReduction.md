# Metric Exponent Reduction

## Abstract

An inverse-linear metric weight lowers a quadratic small-spacing density to an exactly linear asymptotic law.

**Theorem 1.1 (Inverse metric weight lowers exponent two to one).**

$$lambdaw(lambda)\to m,\quad \frac{d(lambda)}{lambda^{2}}\to c,\quad m> 0, c> 0\quad \Rightarrow\quad \frac{w(lambda)d(lambda)}{lambda}\to mc$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MetricExponentReduction.inverse_metric_reduces_quadratic_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the positive-side filter, assume lambda times the metric weight tends to m>0 and the density divided by lambda squared tends to c>0. Their product is exactly the weighted density divided by lambda, so its limiting coefficient is mc>0.

This isolates the source's 'metric eats a power' mechanism without postulating the stated incomplete-Gamma expectation. The pinned Mathlib version has ordinary Gamma but no matching upper incomplete Gamma declaration; the special-function closed form therefore remains outside this theorem.

Repository searches found no pseudo-Hermitian/GUE exponent theorem. Mathlib's Tendsto product law is used directly.

**Theorem 1.2 (The one-power loss is sharp).**

$$w(lambda)=\frac{m}{lambda},\quad d(lambda)=clambda^{2},\quad w(lambda)d(lambda)=mclambda$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MetricExponentReduction.inverse_metric_linear_model_is_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit positive-side model w(lambda)=m/lambda and d(lambda)=c lambda squared realizes the hypotheses. Its weighted density is exactly mc lambda, while division by lambda squared diverges, so the linear exponent cannot be promoted back to a quadratic one.

## References

- Truth anchor: `D5/S3/Quantum/MetricExponentReduction.inverse_metric_linear_model_is_sharp`
- Truth anchor: `D5/S3/Quantum/MetricExponentReduction.inverse_metric_reduces_quadratic_exponent`
