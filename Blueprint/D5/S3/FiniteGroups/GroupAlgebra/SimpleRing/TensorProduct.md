# Tensor simplicity for the group-algebra image argument.

## Abstract

Tensor simplicity for the group-algebra image argument.

`D5/S3/FiniteGroups/GroupAlgebra/SimpleRing/TensorProduct`

The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.

$\forall K \in Type*,\; \forall A \in Type*,\; \forall B \in Type*,\; [Field\left(K\right)], [Ring\left(A\right)], [Algebra\left(K, A\right)], [Ring\left(B\right)], [Algebra\left(K, B\right)], [IsSimpleRing\left(B\right)], [\operatorname{Algebra}.\operatorname{IsCentral}\left(K, B\right)], [IsSimpleRing\left(A\right)], IsSimpleRing\left(\operatorname{Algebra}.\operatorname{TensorProduct}\left(K, A, B\right)\right)$

The tensor product of a simple algebra and a central simple algebra is simple. In the left-central proof, a nonzero tensor coefficient is normalized by a finite left-right multiplier sum. Commutators reduce the support until centrality forces the coefficients into the base field. Ideal extension and contraction then identify every ideal with the ideal induced from the other factor. Tensor symmetry gives the displayed right-central statement. Applied to the actual image and its opposite algebra, it supports Skolem-Noether without assuming an inner implementer.

## References

- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/Operations](../TwoSidedIdeal/Operations.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/SpanAsSum](../TwoSidedIdeal/SpanAsSum.md)
