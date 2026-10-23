# Incomplete beta coefficients

## Abstract

Definitions for the coefficient form of the incomplete beta conjecture.

**Definition 1.1 (Gamma coefficient).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Defs.coeff`

*Formalization.* `D5/S3/Analytic/IncompleteBeta/Defs.coeff` (`✓ std3`).

*Citation.* D. B. Karp (2016). *Normalized incomplete beta function: log-concavity in parameters and other properties*. DOI: [10.1007/s10958-016-2958-z](https://doi.org/10.1007/s10958-016-2958-z). URL: <https://arxiv.org/abs/1509.05120v1>.

*Commentary.*

The coefficient indexed by j is Gamma(a+b+j) divided by the product Gamma(b)Gamma(a+j+1).

**Definition 1.2 (Coefficient difference).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Defs.phi`

*Formalization.* `D5/S3/Analytic/IncompleteBeta/Defs.phi` (`✓ std3`).

*Citation.* D. B. Karp (2016). *Normalized incomplete beta function: log-concavity in parameters and other properties*. DOI: [10.1007/s10958-016-2958-z](https://doi.org/10.1007/s10958-016-2958-z). URL: <https://arxiv.org/abs/1509.05120v1>.

*Commentary.*

The nth coefficient difference is the finite convolution difference obtained from two parameter shifts.

**Definition 1.3 (Positivity claim).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Defs.claim`

*Formalization.* `D5/S3/Analytic/IncompleteBeta/Defs.claim` (`✓ std3`).

*Citation.* D. B. Karp (2016). *Normalized incomplete beta function: log-concavity in parameters and other properties*. DOI: [10.1007/s10958-016-2958-z](https://doi.org/10.1007/s10958-016-2958-z). URL: <https://arxiv.org/abs/1509.05120v1>.

*Commentary.*

For positive real parameters, every finite coefficient difference is positive.

## References

- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Defs.claim`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Defs.coeff`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Defs.phi`
