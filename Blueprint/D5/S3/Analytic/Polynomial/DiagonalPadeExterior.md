# Exterior poles of the diagonal exponential Padé denominator

## Abstract

Parabolic exclusion and the corrected phase separate exterior Padé poles from the full central lattice.

**Theorem 1.1 (Parabolic exclusion).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.denominator_root_norm_add_re`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.denominator_root_norm_add_re` (`✓ std3`). ∎

*Citation.* E. B. Saff and R. S. Varga (1976). *Zero-Free Parabolic Regions for Sequences of Polynomials*. DOI: [10.1137/0507028](https://doi.org/10.1137/0507028). URL: <https://math.vanderbilt.edu/saffeb/texts/22.pdf#page=8>.

*Commentary.*

Every root ζ of the diagonal exponential Padé denominator of natural order m satisfies |ζ| + Re ζ ≥ 2(m+1). Fix the numerator order and vary the denominator degree k. The factorial-scaled reflected polynomials satisfy the continuant recurrence P_(k+2) = (z+m+k+2)P_(k+1) − (k+1)zP_k. In the excluded region their successive ratios have the form z+u with Re u ≥ m+1. Completing a square shows that z+u is nonzero and Re(z/(z+u)) ≤ 1, which closes the induction. At k=m, the exact reversal identifies the reflected polynomial with the native denominator.

**Theorem 1.2 (Uniform separation in scaled radius).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exists_uniform_scaled_exterior_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exists_uniform_scaled_exterior_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* E. B. Saff and R. S. Varga (1976). *Zero-Free Parabolic Regions for Sequences of Polynomials*. DOI: [10.1137/0507028](https://doi.org/10.1137/0507028). URL: <https://math.vanderbilt.edu/saffeb/texts/22.pdf#page=8>.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

Let 0<c<1 be a real zero of the limiting phase η and let ε>0. For all sufficiently large odd m, every scaled pole w=ζ/(2ν) outside the open ε-disk about c satisfies |w|≥c+δ for one δ>0 independent of m. Parabolic exclusion puts the poles with modulus at most a fixed d between c and 1 in a strict right half-plane sector. Along a semicircular arc the derivative of Re η with respect to angle is −Im sqrt(1+w²). The real-axis phase is strictly increasing, so c is the only point of radius at most c in that sector with vanishing real phase. Compactness gives a positive lower bound for max(|w|−c, |Re η(w)|) away from the disk. At a pole the corrected phase is purely imaginary and approximates η uniformly in the sector.

**Definition 1.3 (Exterior pole set).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exteriorPoles`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exteriorPoles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the distinct denominator roots by excluding every value 2ν g(j π i/ν) whose phase norm is at most the full central cutoff.

**Theorem 1.4 (Uniform logarithmic gap and aggregate estimate).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exists_uniform_exterior_pole_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exists_uniform_exterior_pole_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Acknowledgement.* E. B. Saff and R. S. Varga (1976). *Zero-Free Parabolic Regions for Sequences of Polynomials*. DOI: [10.1137/0507028](https://doi.org/10.1137/0507028). URL: <https://math.vanderbilt.edu/saffeb/texts/22.pdf#page=8>.

*Commentary.*

At the positive phase zero 0<c<1, a fixed cutoff, inverse disk, localization disk and positive gap work for every sufficiently large odd order. The analytic inverse gives distinct roots throughout the full cutoff, including every root scaled into the localization disk. The index-zero root r and its residue are positive. For every other pole outside the full cutoff log(|ζ|/r)≥λ for one λ>0. The reference scaled pole converges to c, so the uniform exterior radius bound gives the logarithmic gap. For 1/4≤n/ν²≤1/2 the norm of the normalized exterior sum is at most m exp(−λν²/4). The native residue bound controls each term and the denominator degree bounds their number.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.denominator_root_norm_add_re`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exists_uniform_exterior_pole_gap`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exists_uniform_scaled_exterior_radius`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExterior.exteriorPoles`
- Dependency: [D5/S3/Analytic/HalfIntegerBessel](../HalfIntegerBessel.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeExponential](DiagonalPadeExponential.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadePhase](DiagonalPadePhase.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeResidue](DiagonalPadeResidue.md)
