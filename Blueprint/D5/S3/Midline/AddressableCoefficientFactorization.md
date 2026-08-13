# Addressable Coefficient Factorization

## Abstract

Prime-axis zeta coefficients split pointwise into public half-density, phase, and scaling factors.

**Theorem 1.1 (Every addressable coefficient has the three-factor decomposition).**

$$\forall \delta,t\in\mathbb{R},\ \forall a\in\operatorname{PrimeAxisTable},\ \operatorname{labeledZetaCoefficient}(\frac{1}{2}+\delta+it,a)=\operatorname{labeledZetaCoefficient}(\frac{1}{2},a) \cdot \operatorname{verticalPhase}(t,a) \cdot \operatorname{horizontalWeight}(\delta,a).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/AddressableCoefficientFactorization.addressable_coefficient_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real delta and t and every PrimeAxisTable address a, the concrete coefficient at (1/2 + delta) + it is the product of the coefficient at 1/2, the existing verticalPhase at t, and the existing horizontalWeight at delta. No sign or nonzero hypothesis is needed for this coefficient identity.

The proof unfolds only the public labeledZetaCoefficient, verticalPhase, and horizontalWeight declarations. Positivity of primeAxisEncoding supplies the nonzero base needed to apply Complex.cpow_add twice. It does not invoke the private additive helper inside SpectralDynamics, so this theorem is independently addressable from the public API.

Repository search found OffLineCoefficientScaling.off_line_coefficient_scaling_spec, which factors the generic exponential family labeledZeta and bundles scaling-ledger consequences. It is related but not the concrete prime-axis labeledZetaCoefficient statement using the public phase and weight factors. Pinned Mathlib search found Complex.cpow_add, which is reused directly. The equality is term-wise at one address and asserts nothing about a coefficient sum or analytic continuation.

## References

- Truth anchor: `D5/S3/Midline/AddressableCoefficientFactorization.addressable_coefficient_factorization`
- Dependency: [D5/S3/Weil/SpectralDynamics](../Weil/SpectralDynamics.md)
