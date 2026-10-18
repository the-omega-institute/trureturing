# Finite Perron supplier: Primitive

## Abstract

Finite Perron supplier: Primitive

Apache-2.0 source by Matteo Cipollina, or4nge19/MCMC at b901242fd04b6eff425a177e5c9bc6c56257bc62. The full Apache-2.0 license is reproduced in D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean; the canonical supplier family retains the original copyright notices. Unused declarations are omitted and imports are relocated; the retained mathematical proof is reused without a novelty claim.

At a simplex maximizer of the Collatz-Wielandt function, a nonzero nonnegative residual would become strictly positive under a positive matrix power and produce a larger normalized value. Hence the residual vanishes. The positive power then proves positivity of the eigenvector; row positivity gives a positive eigenvalue. These are the retained upstream Perron proof, directly consumed by the irreducible construction.

## References

- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt](CollatzWielandt.md)
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Lemmas](Lemmas.md)
