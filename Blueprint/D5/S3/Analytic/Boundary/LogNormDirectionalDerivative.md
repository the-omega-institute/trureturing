# Log-Norm Directional Derivative

## Abstract

The logarithmic norm of a nonvanishing holomorphic germ has the directional logarithmic derivative predicted by the complex chain rule.

**Theorem 1.1 (The rotated Riesz potential follows the real logarithmic derivative).**

$$\forall xi: \mathbb{C} \to \mathbb{C}, xiPrime\in\mathbb{C}, x, omega\in\mathbb{R},\\{}\operatorname{let} Xi := (z \mapsto xi\left(\frac{1}{2} - i \times z\right)),\\{}\operatorname{HasDerivAt}\left((u \mapsto \log\left|Xi\left(x + i \times u\right)\right|), \Re(\frac{xiPrime}{xi\left(\frac{1}{2} + omega - i \times x\right)}), omega\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/LogNormDirectionalDerivative.riesz_potential_real_direction_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing Xi(z) = xi(1/2 - i z) rotates the upper-half-plane height into the positive real direction of xi. At a nonzero value, the resulting log-norm potential therefore has derivative Re(xiPrime/xi).

The proof differentiates the squared norm and then applies the real logarithm, so it is valid at every nonzero complex value and does not impose a branch cut for the complex logarithm.

For the unrotated path x + i omega, the same general theorem gives minus the imaginary part instead. The module checks this sign numerically for f(z) = z and f(z) = z squared at 1 + i.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/LogNormDirectionalDerivative.riesz_potential_real_direction_hasDerivAt`
