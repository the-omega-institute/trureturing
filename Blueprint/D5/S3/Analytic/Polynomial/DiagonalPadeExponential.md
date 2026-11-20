# Diagonal exponential Padé denominator

## Abstract

The rational diagonal exponential Padé denominator has an exact half-integer Bessel representation.

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

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.connectionFactor`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_eq_bessel`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.denominator_eq_reverse`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.hasFPowerSeriesAt_reciprocal`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.normalization`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeExponential.reciprocalCoefficient`
- Dependency: [D5/S3/Analytic/HalfIntegerBessel](../HalfIntegerBessel.md)
