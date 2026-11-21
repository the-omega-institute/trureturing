# Diagonal exponential Padé denominator

## Abstract

The rational diagonal exponential Padé denominator has an exact half-integer Bessel representation and its reciprocal coefficients are given by a sum over simple poles.

**Definition 1.1 (Normalized rational denominator).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator` (`✓ std3`).

*Citation.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

For natural m, the coefficient of degree j through m is (-1)^j binom(m,j) (2m-j)!/(2m)!. Terms above m are zero.

**Definition 1.2 (Factorial normalization).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.normalization`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.normalization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factorial factor is m!/(2m)!.

**Theorem 1.3 (Reversal of the finite carrier).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_eq_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_eq_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

Reverse the degree-m carrier P_m, substitute -X/2 and multiply by 2^m m!/(2m)!. The reversal changes index j to m-j and the binomial factorial identity converts the resulting coefficient to the diagonal denominator coefficient.

**Definition 1.4 (Principal square-root factor).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.connectionFactor`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.connectionFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor N_m(z) is m! z^m sqrt(z/pi)/(2m)!, using the principal square root.

**Theorem 1.5 (Exact regular and decaying carrier connection).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_eq_bessel`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_eq_bessel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For every natural m and Re z > 0, N_m(z) is nonzero and the complex denominator equals N_m(z) exp(-z/2) (K_m(z/2) + (-1)^m pi I_m(z/2)). The reflected finite carrier and reversal give the sign and scale. Positive real scaling of the principal root cancels the Bessel prefactor.

**Definition 1.6 (Rational reciprocal coefficient).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.reciprocalCoefficient`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.reciprocalCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

The coefficient is extracted in the rational formal power series ring from the inverse of the normalized denominator.

**Theorem 1.7 (Taylor coefficients of the same reciprocal).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.hasFPowerSeriesAt_reciprocal`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.hasFPowerSeriesAt_reciprocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

After rational-to-complex casting, the formal reciprocal coefficients give the analytic Taylor expansion at zero of the inverse of the complex denominator. The constant coefficient is one. Multiplying the analytic Taylor expansion by the polynomial and comparing the Cauchy product with one identifies the formal inverse. On the right half-plane the denominator has the exact Bessel representation above.

**Theorem 1.8 (Nonzero simple roots and signed derivative).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_root_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_root_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

For every natural m and complex root z of q_m, both z and q_m'(z) are nonzero. The identity q_m(-z) q_m'(z) = (-1)^m (m!/(2m)!)^2 z^(2m) follows by reversing the finite carrier, differentiating at the root, and applying the reflected carrier Wronskian at 2/z.

**Definition 1.9 (Geometric weight of a simple pole).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

The coefficient of the term (1 - z/ζ)^(-1) at a nonzero simple pole ζ is R_m(ζ) = -1/(ζ q_m'(ζ)).

**Theorem 1.10 (Odd-order weight with factorial normalization).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

For every odd m and root ζ, R_m(ζ) equals q_m(-ζ)/((m!/(2m)!)^2 ζ^(2m+1)).

**Theorem 1.11 (Reciprocal coefficients as a sum over distinct roots).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.reciprocalCoefficient_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.reciprocalCoefficient_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

For every positive natural m and natural n, the complex cast of the rational reciprocal coefficient is the sum of R_m(ζ) (ζ^(-1))^n over the distinct complex roots of q_m. Factoring over those roots and applying barycentric Lagrange interpolation to the constant one gives the partial fractions. Geometric expansions near zero and Taylor uniqueness identify their coefficients with the rational formal inverse.

**Theorem 1.12 (Positive weight at a positive real pole).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

For every odd m and positive real root r, R_m(r) is a positive real number. The reflected denominator has nonnegative coefficients and constant term one.

**Theorem 1.13 (Normalized modulus bound).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.norm_normalized_residueWeight_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.norm_normalized_residueWeight_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francesco Scardino (2026). *On a positivity conjecture of Fasi and Higham for Padé approximants to the matrix exponential*. DOI: [10.48550/arXiv.2610.39051](https://doi.org/10.48550/arXiv.2610.39051). URL: <https://arxiv.org/pdf/2610.39051v1#page=1>.

*Commentary.*

For every odd m, natural n, positive real root r, and complex root ζ with r ≤ |ζ|, the modulus of (R_m(ζ)/R_m(r)) (r/ζ)^n is at most (r/|ζ|)^(n+m+1). The reflected coefficients are nonnegative and their powers have degree at most m.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.connectionFactor`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_eq_bessel`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_eq_reverse`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_root_derivative`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.hasFPowerSeriesAt_reciprocal`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.norm_normalized_residueWeight_le`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.normalization`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.reciprocalCoefficient`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.reciprocalCoefficient_eq_sum`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight_eq`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.residueWeight_pos`
- Dependency: [D5/S3/Analytic/HalfIntegerBesselSector](../HalfIntegerBesselSector.md)
