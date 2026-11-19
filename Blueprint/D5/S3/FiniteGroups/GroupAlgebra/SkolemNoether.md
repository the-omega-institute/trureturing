# Inner automorphisms of a finite central simple algebra.

## Abstract

Inner automorphisms of a finite central simple algebra.

`D5/S3/FiniteGroups/GroupAlgebra/SkolemNoether`

The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.

$\forall K \in Type*,\; \forall A \in Type*,\; [Field\left(K\right)], [Ring\left(A\right)], [Algebra\left(K, A\right)], [\operatorname{Module}.\operatorname{Finite}\left(K, A\right)], [\operatorname{Algebra}.\operatorname{IsCentral}\left(K, A\right)], [IsSimpleRing\left(A\right)], \forall e \in AlgEquiv\left(K, A, A\right),\; \exists x \in Units\left(A\right),\; \forall z \in A,\; e\left(z\right) = x \cdot z \cdot \operatorname{Inv}.\operatorname{inv}\left(x\right)$

The Skolem-Noether theorem identifies every algebra automorphism of a finite central simple algebra with conjugation by a unit. The regular representations twisted by the automorphism and by the identity have equal scalar dimensions. Morita theory gives an equivalence; commutation with right multiplication identifies it with multiplication by its value at one. In the representation application the base field is the actual image center, and the unit is obtained only after center-fixing has been proved.

## References

- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/Morita/SimpleRing](Morita/SimpleRing.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/SimpleRing/TensorProduct](SimpleRing/TensorProduct.md)
