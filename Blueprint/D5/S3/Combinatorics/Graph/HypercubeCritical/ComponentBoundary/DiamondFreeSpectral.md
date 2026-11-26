# Spectral rigidity with no shared triangle edge

## Abstract

Spectral rigidity with no shared triangle edge

**Theorem 1.1 (Two-step incidence bound).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral.two_step_incidence_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral.two_step_incidence_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The neighborhood of a vertex has disjoint edges. Every external vertex can touch at most one endpoint of each such edge, giving a sharp finite incidence bound on walks of length two.

**Theorem 1.2 (Eigenvalue four forces eight vertices and rigid equality).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral.card_ge_eight_and_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral.card_ge_eight_and_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a maximum of the positive eigenvector, the two-step row sum is at least sixteen. The incidence bound forces at least eight vertices, and at equality the graph is the complete bipartite graph with two parts of four.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral.card_ge_eight_and_rigidity`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral.two_step_incidence_bound`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap](PrimeContactCardinalityGap.md)
