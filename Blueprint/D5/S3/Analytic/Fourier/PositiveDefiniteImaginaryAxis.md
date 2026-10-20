# Analytic positive definite functions

## Abstract

Imaginary radius bounds from finite positive semidefinite kernels.

**Theorem 1.1 (Exact binomial quadratic moments).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.finite_difference_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.finite_difference_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Furuichi and M. Eghbali Amlashi (2024). *On bounds of logarithmic mean and mean inequality chain*. DOI: [10.7153/mia-2024-27-27](https://doi.org/10.7153/mia-2024-27-27). URL: <https://arxiv.org/abs/2203.01134>.

*Commentary.*

For natural k and m with m at most 2k, put u(j)=(-1)^j choose(k,j) for j from zero to k. The sum over i and j of u(i)u(j)(i-j)^m is zero below degree 2k and is (-1)^k (2k)! at degree 2k. Two successive forward differences give the identity, including the case k=0.

**Theorem 1.2 (The imaginary radius lower bound).**

Lean statement: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Furuichi and M. Eghbali Amlashi (2024). *On bounds of logarithmic mean and mean inequality chain*. DOI: [10.7153/mia-2024-27-27](https://doi.org/10.7153/mia-2024-27-27). URL: <https://arxiv.org/abs/2203.01134>.

*Commentary.*

Let f map the real line to the complex numbers, be real valued, and have a positive semidefinite matrix with entries f(x(j)-x(i)) for every finite real family x. Suppose F is complex differentiable on the open disk of radius R centered at zero and agrees with f at every real x with absolute value less than R. For every real y with 0 at most y and y less than R, the real part of F(iy) is at least the real part of f(0).

Binomial vectors test positive semidefiniteness at arbitrarily small real step sizes. The exact quadratic moments cancel every Taylor term below degree 2k. An analytic Taylor remainder and continuity give nonnegativity of (-1)^k times the even Taylor coefficient. Restriction of the power series to the real line shows that all coefficients are real. Odd powers therefore have zero real part on the imaginary radius, and summation of the nonnegative even terms gives the bound. The real-valued hypothesis is essential to this argument; no boundary regularity is assumed.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.finite_difference_moment`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite`
- Dependency: [D5/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion](../../Weil/ZetaLinear/FiniteInversePoissonCriterion.md)
