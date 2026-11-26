# Recover arbitrary subspace functions from quotient-code moments

## Abstract

Recover arbitrary subspace functions from quotient-code moments.

**Theorem 1.1 (Recover arbitrary subspace functions from quotient-code moments).**

$$\forall f \in \operatorname{RealFunctionsOnSubspaces}\left(\right),\; \forall ell \in \operatorname{SiteLabels}\left(\right),\; \operatorname{ReconstructedPhysicalMoment}\left(ell, f\right) = \operatorname{TargetColumnSpanFunction}\left(f, ell\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/ProjectionMoments.physical_lattice_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite-dimensional space over a finite field, use one diagonal density encoder for every quotient by a subspace. After row scaling, the moment at order one more than the label dimension counts tuples in an intersection. Grouping tuples by their span factors the kernel through the inclusion zeta matrix with a strictly positive diagonal of spanning-tuple counts. This proves invertibility and gives one real coefficient vector for every target scalar function, shared over all selected sets of sites.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/ProjectionMoments.physical_lattice_reconstruction`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalRibbonBoundaryWalsh](DiagonalRibbonBoundaryWalsh.md)
