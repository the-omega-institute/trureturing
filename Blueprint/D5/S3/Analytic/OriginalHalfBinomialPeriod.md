# The original period equation

## Abstract

The complex analytic period of the original half-binomial coefficients.

**Definition 1.1 (The actual period).**

$$\forall z\in \mathbb{C}, \operatorname{period}\left(z\right)=\sum_{n=0}^{\infty}\operatorname{halfBinomial}\left(n\right)^{2}z^{n}$$

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialPeriod.period` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every complex z the period is the infinite sum of halfBinomial(n) squared times z to the n. The coefficient halfBinomial(n) is the original product of -1/2-j for 0 <= j < n divided by n factorial. The definition uses the complex sum, with the usual totalized value when a series is not summable. All convergence and differential claims below are restricted to the open unit disk.

**Theorem 1.2 (The full complex disk equation).**

$$\forall z\in \mathbb{C}, \Vert z \Vert<1\Rightarrow \operatorname{DifferentiableAt}\left(\mathbb{C}, period, z\right)\land \operatorname{DifferentiableAt}\left(\mathbb{C}, \operatorname{deriv}\left(period\right), z\right)\land z(1-z)(\operatorname{deriv}\left(\operatorname{deriv}\left(period\right)\right))(z)+(1-2z)(\operatorname{deriv}\left(period\right))(z)-\frac{1}{4}\operatorname{period}\left(z\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialPeriod.picard_fuchs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex z of norm less than one, both the period and its first complex derivative are complex differentiable, and z(1-z) times its second derivative plus (1-2z) times its first derivative minus one quarter times the period equals zero. Zero is included; the argument never divides by z.

The original successor recurrence gives the exact square-coefficient recurrence (n+1)^2 c(n+1)=(n+1/2)^2 c(n) and bounds the coefficient norms by one. On any smaller disk, polynomially weighted geometric series dominate the original and shifted derivative series. The complex locally uniform series theorems justify differentiation twice. Reindexing these convergent sums identifies the two sides coefficient by coefficient.

The equation is the classical Gauss hypergeometric differential equation with a=b=1/2 and c=1, as in DLMF 15.10.1. The result here establishes it for the literal original factorial-product coefficients over the full complex unit disk. It does not identify a native operator resolvent, determine a boundary logarithmic constant or nome, or establish a conformal field theory or string realization.

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialPeriod.period`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialPeriod.picard_fuchs`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](../VertexAlgebra/LatticeHalfFockFiniteCorrection.md)
