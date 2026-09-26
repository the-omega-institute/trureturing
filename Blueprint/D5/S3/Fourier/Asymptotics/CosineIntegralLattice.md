# Cosine Integral on Positive Lattices

## Abstract

The squared cosine-integral tail has a uniform bound on every positive lattice.

**Definition 1.1 (The real cosine-integral tail).**

$$\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{Ci}\left(x\right) = \frac{\operatorname{sin}\left(x\right)}{x} - \int_{x}^{\infty} \frac{\operatorname{sin}\left(t\right)}{t^{2}} dt$$

*Formalization.* `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive x, the integral of sin(t) / t^2 over (x,infinity) is absolutely convergent. The displayed representation has the usual convention Ci(x) equal to the negative improper integral of cos(t)/t from x to infinity. Integration by parts gives the sine boundary term with a positive sign and the remaining tail with a negative sign. The Lean definition is a total real function; the analytic interpretation here concerns positive arguments.

**Theorem 1.2 (One constant for all positive spacings).**

$$\exists C \in \mathbb{R},\; 0 < C \land \left(\forall z \in \mathbb{R},\; 0 < z \Rightarrow \left(\operatorname{Summable}\left(n:\mathbb{N} \mapsto \operatorname{Ci}\left(z \cdot (n+1)\right)^{2}\right) \land z \cdot \sum_{n \in \mathbb{N}} \operatorname{Ci}\left(z \cdot (n+1)\right)^{2} \le C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one positive real constant C, independent of the positive spacing z. The infinite series of squared Ci values at z,2z,3z,... is summable, and its sum multiplied by z is at most C.

The elementary sine bounds imply absolute Ci bounds 5 times x to the power -1/4 and 2/x for every positive x. Squaring gives the nonnegative envelope E(x)=25 x^(-1/2) for 0<x<=1 and E(x)=25 x^(-2) for x>1. The two formulas agree at one. This envelope is decreasing and integrable on the positive half-line, and x E(x) is at most 25.

Separate the first lattice point and compare the remaining terms with the integral from z to infinity. A change of variables cancels the factor z. The proof chooses C=26 plus the integral of E over the positive half-line. No lower bound on z and no finite truncation of the series is required. The statement is a deterministic analytic estimate and contains no stochastic convergence assertion.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineIntegralLattice.result`
