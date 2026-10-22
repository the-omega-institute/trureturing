# Definitions and parameter classifications

## Abstract

Zero-balanced Gauss quotients

**Definition 1.1 (The Gauss hypergeometric function).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Defs.gauss`

*Formalization.* `D5/S3/Analytic/GaussZeroBalanced/Defs.gauss` (`✓ std3`).

*Citation.* S.-L. Qiu, X.-Y. Ma and X.-Y. Xiang (2024). *Turán-type inequalities for Gaussian hypergeometric functions, and Baricz's conjecture*. DOI: [10.48550/arXiv.2408.15723](https://doi.org/10.48550/arXiv.2408.15723). URL: <https://arxiv.org/abs/2408.15723>.

*Commentary.*

For real a, b, c and x, gauss a b c x is Mathlib ordinaryHypergeometric over the real numbers. Its defining coefficients are the ascending Pochhammer products divided by the denominator product and the factorial.

**Definition 1.2 (The zero-balanced quotient).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Defs.quot`

*Formalization.* `D5/S3/Analytic/GaussZeroBalanced/Defs.quot` (`✓ std3`).

*Citation.* S.-L. Qiu, X.-Y. Ma and X.-Y. Xiang (2024). *Turán-type inequalities for Gaussian hypergeometric functions, and Baricz's conjecture*. DOI: [10.48550/arXiv.2408.15723](https://doi.org/10.48550/arXiv.2408.15723). URL: <https://arxiv.org/abs/2408.15723>.

*Commentary.*

For real a, b and x, quot a b x is gauss (a+1) (b+1) (a+b+1) x divided by gauss a b (a+b) x.

**Definition 1.3 (The contiguous quotient).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Defs.f`

*Formalization.* `D5/S3/Analytic/GaussZeroBalanced/Defs.f` (`✓ std3`).

*Citation.* S.-L. Qiu, X.-Y. Ma and X.-Y. Xiang (2024). *Turán-type inequalities for Gaussian hypergeometric functions, and Baricz's conjecture*. DOI: [10.48550/arXiv.2408.15723](https://doi.org/10.48550/arXiv.2408.15723). URL: <https://arxiv.org/abs/2408.15723>.

*Commentary.*

For real a, b and x, f a b x is gauss a b (a+b+1) x divided by gauss a b (a+b) x.

**Definition 1.4 (The shifted-parameter comparison).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Defs.ineq17`

*Formalization.* `D5/S3/Analytic/GaussZeroBalanced/Defs.ineq17` (`✓ std3`).

*Citation.* S.-L. Qiu, X.-Y. Ma and X.-Y. Xiang (2024). *Turán-type inequalities for Gaussian hypergeometric functions, and Baricz's conjecture*. DOI: [10.48550/arXiv.2408.15723](https://doi.org/10.48550/arXiv.2408.15723). URL: <https://arxiv.org/abs/2408.15723>.

*Commentary.*

For real a and r, ineq17 a r compares gauss (a+1) (2-a) 2 r / gauss a (1-a) 1 r strictly above gauss (a+1) (5/2-a) (5/2) r / gauss a (3/2-a) (3/2) r.

**Definition 1.5 (The two parameter classifications).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Defs.claim`

*Formalization.* `D5/S3/Analytic/GaussZeroBalanced/Defs.claim` (`✓ std3`).

*Citation.* S.-L. Qiu, X.-Y. Ma and X.-Y. Xiang (2024). *Turán-type inequalities for Gaussian hypergeometric functions, and Baricz's conjecture*. DOI: [10.48550/arXiv.2408.15723](https://doi.org/10.48550/arXiv.2408.15723). URL: <https://arxiv.org/abs/2408.15723>.

*Commentary.*

The first clause quantifies over all positive real a and b: the derivative in b of quot a b x is strictly negative at every real x in (0,1) if and only if b is at most sqrt(a(a+1)). The second clause quantifies over every real a in (0,1): ineq17 a r holds at every real r in (0,1) if and only if a is at least 3/7.

## References

- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Defs.claim`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Defs.f`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Defs.gauss`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Defs.ineq17`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Defs.quot`
