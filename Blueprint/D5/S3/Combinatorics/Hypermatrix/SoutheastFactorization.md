# Constructive southeast Bruhat factors

## Abstract

Constructive southeast Bruhat factors

**Theorem 1.1 (Constructive southeast Bruhat factors).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/SoutheastFactorization.southeast_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypermatrix/SoutheastFactorization.southeast_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Over every field F, a matrix in GL(n plus one,F) has an upper triangular factor and a residual matrix whose first column has a single pivot one at p; deleting that row and first column gives a matrix in GL(n,F). The pivot is the largest row with a nonzero original first-column entry. Every G in GL(n,F) can be written U B, where U is upper triangular and B has southeast shape for a permutation sigma. If A and C have southeast shapes for sigma and tau and A=U C with U upper triangular, then sigma=tau, A=C and U=1. The proof constructs pivots and inducts on n; uniqueness follows by descending through the row pivots. The zero-dimensional case is retained.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/SoutheastFactorization.southeast_factorization`
- Dependency: [D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs](MaskedFacesDefs.md)
