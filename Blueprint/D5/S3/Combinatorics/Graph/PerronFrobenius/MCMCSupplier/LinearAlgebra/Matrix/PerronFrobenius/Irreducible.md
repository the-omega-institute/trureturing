# Finite Perron supplier: Irreducible

## Abstract

Finite Perron supplier: Irreducible

Apache-2.0 source by Matteo Cipollina, or4nge19/MCMC at b901242fd04b6eff425a177e5c9bc6c56257bc62. The full Apache-2.0 license is reproduced in D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean; the canonical supplier family retains the original copyright notices. Unused declarations are omitted and imports are relocated; the retained mathematical proof is reused without a novelty claim.

Transport paths along inclusion of positive supports to show that 1+A is irreducible. Its positive diagonal makes it primitive. Apply the retained primitive positive-eigenvector result and subtract the identity; an actual positive entry of A proves that the shifted eigenvalue exceeds one. This constructs a positive eigenpair for A without assuming that A is primitive.

## References

- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Lemmas](Lemmas.md)
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Primitive](Primitive.md)
