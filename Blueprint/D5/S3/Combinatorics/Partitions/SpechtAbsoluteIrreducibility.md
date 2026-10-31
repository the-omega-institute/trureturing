# Specht AbsoluteIrreducibility

## Abstract

Specht AbsoluteIrreducibility

The invariant orthogonal decomposition gives a preimage of each polytabloid inside the Specht subspace under its column antisymmetrizer. An equivariant endomorphism commutes with this operator, whose image is a single polytabloid line. It acts by one scalar on that polytabloid. The orbit spans the entire Specht space, forcing the same scalar everywhere. Transport to the original partition identifies rational Specht intertwining endomorphisms with the rational field.

EndIntertwiner denotes the algebra of equivariant endomorphisms of the indicated representation; rationalScalarMap sends a rational number to its scalar endomorphism. The final algebra equivalence is the inverse of that bijective scalar map. columnAntisymmetrizerAction is the group-algebra action of the displayed tableau column antisymmetrizer on the rational permutation space.

**Theorem 1.1 (exists mem asAlgebraHom columnAntisymmetrizer eq polytabloid).**

$$\forall mu \in \operatorname{YoungDiagram},\; \forall t \in \operatorname{YoungTableau}\left(mu\right),\; \exists e \in \operatorname{permutationSpace}\left(\operatorname{shapePartition}\left(mu\right)\right),\; \operatorname{member}\left(e, \operatorname{spechtSubspace}\left(mu\right)\right) \land \operatorname{columnAntisymmetrizerAction}\left(t, e\right) = \operatorname{polytabloid}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

**Theorem 1.2 (algebraMap intertwiningMap spechtSubrepresentation bijective).**

$$\forall mu \in \operatorname{YoungDiagram},\; \operatorname{Bijective}\left(\operatorname{rationalScalarMap}\left(\operatorname{EndIntertwiner}\left(\operatorname{spechtSubrepresentation}\left(mu\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.algebraMap_intertwiningMap_spechtSubrepresentation_bijective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

**Theorem 1.3 (algebraMap intertwiningMap spechtModule bijective).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \operatorname{Bijective}\left(\operatorname{rationalScalarMap}\left(\operatorname{EndIntertwiner}\left(\operatorname{spechtModule}\left(mu\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.algebraMap_intertwiningMap_spechtModule_bijective` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

**Definition 1.4 (spechtModuleIntertwiningEndAlgEquiv).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \operatorname{spechtModuleIntertwiningEndAlgEquiv}\left(mu\right) = \operatorname{inverseRationalScalarAlgebraEquivalence}\left(\operatorname{spechtModule}\left(mu\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.spechtModuleIntertwiningEndAlgEquiv` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The statement is the selected structural result for the explicit permutation representation and polytabloid construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.algebraMap_intertwiningMap_spechtModule_bijective`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.algebraMap_intertwiningMap_spechtSubrepresentation_bijective`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.spechtModuleIntertwiningEndAlgEquiv`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtSubmoduleTheorem](SpechtSubmoduleTheorem.md)
