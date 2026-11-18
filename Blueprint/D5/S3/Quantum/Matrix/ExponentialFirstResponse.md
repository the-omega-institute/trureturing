# Matrix exponential first response

## Abstract

The first response of measurable evolution gives the operator-norm derivative of the exponential on finite complex matrices.

**Definition 1.1 (Bochner derivative operator).**

Lean statement: `D5/S3/Quantum/Matrix/ExponentialFirstResponse.derivative`

*Formalization.* `D5/S3/Quantum/Matrix/ExponentialFirstResponse.derivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The derivative operator at A is the interval integral of the complex continuous linear maps that multiply H on the left by exp((1−u)A) and on the right by exp(uA). The matrix norm is the L2 operator norm.

**Theorem 1.2 (Derivative applied to a perturbation).**

Lean statement: `D5/S3/Quantum/Matrix/ExponentialFirstResponse.derivative_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ExponentialFirstResponse.derivative_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation on an arbitrary complex matrix H commutes with the interval integral. The resulting matrix integral is the one used in the faithful logarithmic-mean identification.

**Theorem 1.3 (Fréchet derivative at every matrix).**

Lean statement: `D5/S3/Quantum/Matrix/ExponentialFirstResponse.hasFDerivAt_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ExponentialFirstResponse.hasFDerivAt_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential has the full complex Fréchet derivative given by this operator at every A. For the identity contraction and a constant generator, the exponential orbit solves the native mild equation. Continuous residual uniqueness identifies it with the measurable evolution. The original first-response remainder bounds the defect on every Euclidean vector with the same coefficient. Taking the operator norm gives a quadratic bound in the perturbation.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ExponentialFirstResponse.derivative`
- Truth anchor: `D5/S3/Quantum/Matrix/ExponentialFirstResponse.derivative_apply`
- Truth anchor: `D5/S3/Quantum/Matrix/ExponentialFirstResponse.hasFDerivAt_exp`
- Dependency: [D5/S3/Quantum/Analysis/MeasurableFirstResponse](../Analysis/MeasurableFirstResponse.md)
