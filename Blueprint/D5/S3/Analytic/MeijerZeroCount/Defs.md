# The zero-count comparison

## Abstract

Gamma quotients and their inverse Mellin zero counts.

**Definition 1.1 (The Gamma quotient).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Defs.gammaQuot`

*Formalization.* `D5/S3/Analytic/MeijerZeroCount/Defs.gammaQuot` (`✓ std3`).

*Citation.* D. B. Karp and E. G. Prilepkina (2016). *Completely monotonic gamma ratio and infinitely divisible H-function of Fox*. DOI: [10.1007/s40315-015-0128-9](https://doi.org/10.1007/s40315-015-0128-9). URL: <https://arxiv.org/abs/1501.05388>.

*Commentary.*

For real parameter vectors a and b of length p, the quotient is the product of Gamma(a(i)+s) divided by the product of Gamma(b(i)+s).

**Definition 1.2 (The inverse Mellin transform).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Defs.meijerG`

*Formalization.* `D5/S3/Analytic/MeijerZeroCount/Defs.meijerG` (`✓ std3`).

*Citation.* D. B. Karp and E. G. Prilepkina (2016). *Completely monotonic gamma ratio and infinitely divisible H-function of Fox*. DOI: [10.1007/s40315-015-0128-9](https://doi.org/10.1007/s40315-015-0128-9). URL: <https://arxiv.org/abs/1501.05388>.

*Commentary.*

The function is the inverse Mellin transform of the Gamma quotient along the vertical line of real part one, with normalization one divided by two pi in the real integral.

**Definition 1.3 (The control function).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Defs.control`

*Formalization.* `D5/S3/Analytic/MeijerZeroCount/Defs.control` (`✓ std3`).

*Citation.* D. B. Karp and E. G. Prilepkina (2016). *Completely monotonic gamma ratio and infinitely divisible H-function of Fox*. DOI: [10.1007/s40315-015-0128-9](https://doi.org/10.1007/s40315-015-0128-9). URL: <https://arxiv.org/abs/1501.05388>.

*Commentary.*

The control function at t is the sum of t to the power a(i) minus t to the power b(i). These powers are real powers.

**Definition 1.4 (The zero-count comparison).**

Lean statement: `D5/S3/Analytic/MeijerZeroCount/Defs.claim`

*Formalization.* `D5/S3/Analytic/MeijerZeroCount/Defs.claim` (`✓ std3`).

*Citation.* D. B. Karp and E. G. Prilepkina (2016). *Completely monotonic gamma ratio and infinitely divisible H-function of Fox*. DOI: [10.1007/s40315-015-0128-9](https://doi.org/10.1007/s40315-015-0128-9). URL: <https://arxiv.org/abs/1501.05388>.

*Commentary.*

For every positive-length or empty real parameter vector a with nonnegative entries and every real vector b with sum of b(i)-a(i) greater than one, the cardinality of the zero set of the inverse Mellin transform in the unit interval is at most the cardinality of the zero set of the control function there. Cardinalities take values in the extended natural numbers, so infinite zero sets are included. The greater-than-one condition restricts the greater-than-zero parameter range of the conjecture.

## References

- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Defs.claim`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Defs.control`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Defs.gammaQuot`
- Truth anchor: `D5/S3/Analytic/MeijerZeroCount/Defs.meijerG`
