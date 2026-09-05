# Archimedean Observer-Product Positivity

## Abstract

Every nonzero regulator mode has a strictly positive Archimedean observer product.

**Theorem 1.1 (Nonzero modes have positive Archimedean cost).**

$$\forall sigma, tau\in \mathbb{R}, 0 < sigma, \neg tau = 0 \Rightarrow 0 < \sum_{m=0}^{\infty} \operatorname{log}\left(1 + \frac{tau^{2}}{(sigma + 2m)^{2}}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/ArchimedeanObserverProductPositive.archimedean_observer_product_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive offset sigma and a nonzero regulator mode tau, every summand is nonnegative and the zeroth summand is strictly positive.

The logarithm is bounded above by its nonnegative increment, while the increments are controlled by the convergent p-series of exponent two. Summability and the positive zeroth term therefore make the entire infinite sum strictly positive.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/ArchimedeanObserverProductPositive.archimedean_observer_product_positive`
- Dependency: [D5/S3/Weil/ZetaGamma/MasslessTangentConeLimit](MasslessTangentConeLimit.md)
