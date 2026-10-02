# Kernel Recurrence for 1322 Avoidance

## Abstract

The catalytic equation yields a quadratic and cubic coefficient recurrence.

**Theorem 1.1 (Coefficient recurrence from the catalytic equation).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoKernel.catalytic_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoKernel.catalytic_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Let S be a rational power series with constant coefficient one, let C be the Catalan series evaluated at xu, and suppose a series F with polynomial coefficients in u satisfies (1 - u + x times u squared times (S + C)) times F = 1 - u + xu times S squared + x times u squared times C times S. For every positive n, the coefficient s_n of S equals the sum of s_i times s_(n-i) over positive i smaller than n, plus the sum of s_i times s_j times s_k over nonnegative triples with i + j + k = n - 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoKernel.catalytic_recurrence`
