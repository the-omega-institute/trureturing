# Strict positivity in the odd diagonal Padé window

## Abstract

The reciprocal of the normalized diagonal exponential Padé denominator has strictly positive rational coefficients throughout the closed quadratic window at all sufficiently large odd orders.

**Theorem 1.1 (Uniform theta lower bound).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeWindow.theta_real_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeWindow.theta_real_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 20.7.32, modular transformation of the third Jacobi theta function*. URL: <https://dlmf.nist.gov/20.7.E32>.

*Commentary.*

For any c>0 put C=π²c²/(2(1+c²)²). For every τ in [1/4,1/2] and every real phase θ the real part of the sum over integers j of exp(−Cτj²+ijθ) is at least sqrt(2π/C) exp(−π²/C)>0. The Gaussian Poisson identity gives a positive periodized sum. The integer nearest to θ/(2π) supplies the lower bound.

**Theorem 1.2 (Eventual strict rational positivity).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeWindow.exists_uniform_reciprocalCoefficient_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeWindow.exists_uniform_reciprocalCoefficient_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

There exists a natural threshold M such that for all odd natural m≥M and natural n with 1/4≤n/(m+1/2)²≤1/2, the native rational reciprocal coefficient is strictly positive. The central comparison and exterior separation use the same inverse, cutoff, reference pole and positive weight. On a fixed finite set the Gaussian comparison error decreases with m, and the central modulus bound controls the remaining lattice indices by a summable Gaussian. The exterior poles have a uniform logarithmic gap. The four errors, including the omitted theta terms, total at most half the uniform theta lower bound. The exact coefficient identity and the positive normalization transfer this estimate to the rational formal reciprocal.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeWindow.exists_uniform_reciprocalCoefficient_pos`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeWindow.theta_real_lower_bound`
- Dependency: [D5/S3/Analytic/HalfIntegerBessel](../HalfIntegerBessel.md)
- Dependency: [D5/S3/Analytic/HalfIntegerBesselSector](../HalfIntegerBesselSector.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeExponential](DiagonalPadeExponential.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeExterior](DiagonalPadeExterior.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeResidue](DiagonalPadeResidue.md)
