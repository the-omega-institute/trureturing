# Nonvanishing Indices at Minus Two

## Abstract

The nonvanishing indices of the binary digit Hankel determinants at t = -2 are exactly the triples around ceil(2^(k+2)/3).

**Theorem 1.1 (The exact nonvanishing indices).**

Lean statement: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bartosz Sobolewski, Maciej Ulas (2026). *Hankel determinants of weighted binary sums of digits*. DOI: [10.48550/arXiv.2607.09376](https://doi.org/10.48550/arXiv.2607.09376). URL: <https://arxiv.org/abs/2607.09376v1>.

*Commentary.*

For a nonnegative integer u with binary digits epsilon_j, let S(u,t) = sum_j epsilon_j t^j, and let H(n,t) = det(S(i+j,t)) for indices i and j from zero to n minus one. Put n_k = ceil(2^(k+2)/3) for every nonnegative integer k. For every integer n at least two, H(n,-2) is nonzero if and only if n is one of n_k - 1, n_k, or n_k + 1 for some nonnegative integer k. This establishes the case d = 2 of Conjecture 5.7 in Section 5.1 of Sobolewski and Ulas's paper, arXiv:2607.09376v1. Sparse binary kernel vectors force vanishing outside the triples. Reflection recurrences and simultaneous determinant evaluations show that all three members of each triple are nonzero, with the first two triples evaluated directly. The statement concerns t = -2; the equivalence for t = 2 times a primitive root of unity of higher order is not asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel.result`
- Dependency: [D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero](BinaryDigitHankelNonzero.md)
