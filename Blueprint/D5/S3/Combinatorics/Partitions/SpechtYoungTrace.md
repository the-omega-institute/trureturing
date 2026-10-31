# Shape distinction and orthogonality of actual ordinary Specht traces

## Abstract

Shape distinction and orthogonality of actual ordinary Specht traces

Here SComplex(mu) is exactly the existing complex scalar extension of the rational polytabloid representation for YoungDiagram.ofPartition mu. MComplex(nu) is the existing complex representation on cosets of the literal Young subgroup. The complex Hom dimensions vanish outside dominance and equal one on the diagonal, by the rational multiplicity calculation and equality of the actual character pairings under the rational to complex map. An isomorphism of two Specht modules would preserve those Hom dimensions, forcing dominance in both directions and hence equality of the literal partition labels. The pinned finite group character orthogonality theorem then uses the established simplicity of these same representations. trace(mu,pi) means LinearMap.trace over Complex of the existing action rho of SComplex(mu) at pi. The sum includes all permutations, including fixed points; the inverse is the group inverse. No ordinary character is defined by a polynomial coefficient.

**Theorem 1.1 (The actual modules retain their shape labels).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \forall nu \in \operatorname{Partition}\left(n\right),\; \operatorname{Iff}\left(\operatorname{Nonempty}\left(\operatorname{Iso}\left(\operatorname{SComplex}\left(mu\right), \operatorname{SComplex}\left(nu\right)\right)\right), mu = nu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtYoungTrace.spechtModuleℂ_iso_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The notation has the meanings specified above.

**Theorem 1.2 (Ordinary trace row orthogonality).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \forall nu \in \operatorname{Partition}\left(n\right),\; \operatorname{sumPerm}\left(n, \operatorname{traceProductWithInverse}\left(mu, nu\right)\right) = \operatorname{ifThenElse}\left(mu = nu, \operatorname{complexNatCast}\left(\operatorname{factorial}\left(n\right)\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtYoungTrace.sum_spechtTrace_mul_spechtTrace_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The notation has the meanings specified above.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtYoungTrace.spechtModuleℂ_iso_iff`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtYoungTrace.sum_spechtTrace_mul_spechtTrace_inv`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtFrobeniusPairing](SpechtFrobeniusPairing.md)
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtYoungMultiplicity](SpechtYoungMultiplicity.md)
