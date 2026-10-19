# Finite Perron supplier: Path

## Abstract

Finite Perron supplier: Path

Apache-2.0 source by Matteo Cipollina, or4nge19/MCMC at b901242fd04b6eff425a177e5c9bc6c56257bc62. The full Apache-2.0 license is reproduced in D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean; the canonical supplier family retains the original copyright notices. Unused declarations are omitted and imports are relocated; the retained mathematical proof is reused without a novelty claim.

A shortest path between distinct endpoints has no repeated vertex: splitting at a repeated vertex removes a positive-length segment and contradicts minimality. The resulting length bound and loop replication supply fixed-length paths for an irreducible matrix with positive diagonal. The path helpers are used by that argument; unrestricted weighted-walk enumeration is outside this result.

## References

- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Data/List](../../Data/List.md)
