# First parameter coefficient differences

## Abstract

Coefficient inequalities for real shifts of the first incomplete beta parameter.

**Definition 1.1 (Coefficient difference).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Defs.psi`

*Formalization.* `D5/S3/Analytic/IncompleteBetaShape/Defs.psi` (`✓ std3`).

*Citation.* D. B. Karp (2016). *Normalized incomplete beta function: log-concavity in parameters and other properties*. DOI: [10.1007/s10958-016-2958-z](https://doi.org/10.1007/s10958-016-2958-z). URL: <https://arxiv.org/abs/1509.05120v1>.

*Commentary.*

The nth coefficient is the sum, for k from zero to n, of c_k(a+alpha,b)c_(n-k)(a+beta,b) minus c_k(a,b)c_(n-k)(a+alpha+beta,b). The Gamma coefficient c is reused from the incomplete beta coefficient definitions. By the series expansion and product identity, this is the coefficient of x^n after division of the product difference by x^(2a+alpha+beta)(1-x)^(2b). It is independent of x, so the source's restriction on x imposes no further condition on the coefficient.

**Definition 1.2 (Strict signs for positive real shifts).**

Lean statement: `D5/S3/Analytic/IncompleteBetaShape/Defs.claim`

*Formalization.* `D5/S3/Analytic/IncompleteBetaShape/Defs.claim` (`✓ std3`).

*Citation.* D. B. Karp (2016). *Normalized incomplete beta function: log-concavity in parameters and other properties*. DOI: [10.1007/s10958-016-2958-z](https://doi.org/10.1007/s10958-016-2958-z). URL: <https://arxiv.org/abs/1509.05120v1>.

*Commentary.*

For every positive a, b, alpha and beta and every natural n, the coefficient difference is negative when b is less than one and positive when b is greater than one.

## References

- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Defs.claim`
- Truth anchor: `D5/S3/Analytic/IncompleteBetaShape/Defs.psi`
- Dependency: [D5/S3/Analytic/IncompleteBeta/Defs](../IncompleteBeta/Defs.md)
