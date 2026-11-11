# Analytic positive definite functions

## Abstract

Imaginary radius bounds from finite positive semidefinite kernels.

**Definition 1.1 (Binomial stencil weight).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.weight`

*Formalization.* `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural k and j, weight(k,j)=(-1)^j choose(k,j).

**Theorem 1.2 (Signed forward difference).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.weighted_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.weighted_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real function g, natural k and real x, the sum of weight(k,j)g(x+j) over 0<=j<=k equals (-1)^k times the k-fold unit forward difference of g at x.

**Theorem 1.3 (Two-stencil convolution).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.double_weighted_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.double_weighted_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real function g and natural k, the double sum of weight(k,i)weight(k,j)g(i-j) over 0<=i,j<=k equals (-1)^k times the 2k-fold unit forward difference of g at -k.

**Theorem 1.4 (Exact binomial quadratic moments).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.finite_difference_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.finite_difference_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Furuichi and M. Eghbali Amlashi (2024). *On bounds of logarithmic mean and mean inequality chain*. DOI: [10.7153/mia-2024-27-27](https://doi.org/10.7153/mia-2024-27-27). URL: <https://arxiv.org/abs/2203.01134>.

*Commentary.*

For natural k and m with m at most 2k, put u(j)=(-1)^j choose(k,j) for j from zero to k. The sum over i and j of u(i)u(j)(i-j)^m is zero below degree 2k and is (-1)^k (2k)! at degree 2k. Two successive forward differences give the identity, including the case k=0.

**Lemma 1.5 (All Taylor coefficients of a real-preserving germ).**

$$\forall F \in Complex \to Complex,\; \operatorname{AnalyticAt}\left(Complex, F, 0\right) \land \operatorname{EventuallyRealOnRealAxis}\left(F\right) \implies \operatorname{AnalyticAt}\left(Real, \operatorname{realRestriction}\left(F\right), 0\right) \land \forall n \in Nat,\; \operatorname{im}\left(\operatorname{div}\left(\operatorname{iteratedDeriv}\left(n, F, 0\right), \operatorname{factorial}\left(Complex, n\right)\right)\right) = 0 \land \operatorname{re}\left(\operatorname{div}\left(\operatorname{iteratedDeriv}\left(n, F, 0\right), \operatorname{factorial}\left(Complex, n\right)\right)\right) = \operatorname{div}\left(\operatorname{iteratedDeriv}\left(n, \operatorname{realRestriction}\left(F\right), 0\right), \operatorname{factorial}\left(Real, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.real_taylor_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be complex analytic at zero, with imaginary part zero at every real argument in some neighborhood of zero. Its real restriction is the real function x mapped to Re(F(x)), with the real argument embedded in the complex numbers. This restriction is real analytic at zero. For every natural n, the complex coefficient iteratedDeriv(n,F,0)/n! has imaginary part zero and real part equal to the corresponding derivative coefficient of the real restriction. Degree zero is included. The construction precomposes the scalar-restricted series by the real-to-complex continuous linear embedding before projecting real and imaginary parts.

**Theorem 1.6 (The imaginary radius lower bound).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Furuichi and M. Eghbali Amlashi (2024). *On bounds of logarithmic mean and mean inequality chain*. DOI: [10.7153/mia-2024-27-27](https://doi.org/10.7153/mia-2024-27-27). URL: <https://arxiv.org/abs/2203.01134>.

*Commentary.*

Let f map the real line to the complex numbers, be real valued, and have a positive semidefinite matrix with entries f(x(j)-x(i)) for every finite real family x. Suppose F is complex differentiable on the open disk of radius R centered at zero and agrees with f at every real x with absolute value less than R. For every real y with 0 at most y and y less than R, the real part of F(iy) is at least the real part of f(0).

Binomial vectors test positive semidefiniteness at arbitrarily small real step sizes. The exact quadratic moments cancel every Taylor term below degree 2k. An analytic Taylor remainder and continuity give nonnegativity of (-1)^k times the even Taylor coefficient. Restriction of the power series to the real line shows that all coefficients are real. Odd powers therefore have zero real part on the imaginary radius, and summation of the nonnegative even terms gives the bound. The real-valued hypothesis is essential to this argument; no boundary regularity is assumed.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.double_weighted_shift`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.finite_difference_moment`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.real_taylor_data`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.weight`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.weighted_shift`
- Dependency: [D5/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion](../../Weil/ZetaLinear/FiniteInversePoissonCriterion.md)
