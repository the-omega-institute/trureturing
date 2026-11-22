# The singular four-spectrum refined BMV product bound

## Abstract

The singular four-spectrum refined BMV product bound

**Theorem 1.1 (The product bound in every positive degree).**

Lean statement: `D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Endpoint.product_bound_singular_all`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Endpoint.product_bound_singular_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Hägele (2026). *On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices*. DOI: [10.48550/arXiv.2611.00129](https://doi.org/10.48550/arXiv.2611.00129). URL: <https://arxiv.org/abs/2611.00129v1>.

*Commentary.*

For every positive integer p and every pair of complex positive semidefinite matrices A and B of the same finite size, assume A is singular and has at most four distinct eigenvalues, with arbitrary multiplicities. The mean trace of all words with p copies of A and three copies of B is at least the trace of the cube of A^(p/3) B, with A^(p/3) defined by spectral calculus. The repository proof addresses this spectral class of the product comparison discussed in Hägele's Section 7. At the zero center, scalar curvature bounds give a finite interval Gram decomposition. Each positive center has at most two distinct larger eigenvalues, where the ordered quartic and the corner inequality give a two-by-two positive semidefinite block. The cyclic trace-defect identity and the Schur product theorem give the matrix comparison.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Endpoint.product_bound_singular_all`
- Dependency: [D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic](../../RefinedBMVExtremeAnalytic.md)
