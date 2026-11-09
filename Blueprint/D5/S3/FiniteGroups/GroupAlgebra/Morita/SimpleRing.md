# Dimensions determine modules over a finite simple algebra.

## Abstract

Dimensions determine modules over a finite simple algebra.

`D5/S3/FiniteGroups/GroupAlgebra/Morita/SimpleRing`

The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.

$\forall K \in Type*,\; \forall A \in Type*,\; [Field\left(K\right)], [Ring\left(A\right)], [Algebra\left(K, A\right)], [IsSimpleRing\left(A\right)], [\operatorname{Module}.\operatorname{Finite}\left(K, A\right)], \forall M \in Type*,\; \forall N \in Type*,\; [AddCommGroup\left(M\right)], [Module\left(A, M\right)], [Module\left(K, M\right)], [IsScalarTower\left(K, A, M\right)], [\operatorname{Module}.\operatorname{Finite}\left(A, M\right)], [AddCommGroup\left(N\right)], [Module\left(A, N\right)], [Module\left(K, N\right)], [IsScalarTower\left(K, A, N\right)], [\operatorname{Module}.\operatorname{Finite}\left(A, N\right)], Nonempty\left(LinearEquiv\left(\operatorname{RingHom}.\operatorname{id}\left(A\right), M, N\right)\right) \Leftrightarrow \operatorname{Module}.\operatorname{finrank}\left(K, M\right) = \operatorname{Module}.\operatorname{finrank}\left(K, N\right)$

Over a finite-dimensional simple algebra, finite modules are equivalent exactly when their dimensions over the base field agree. Matrix Morita equivalence expresses both as sums of one simple module. Finite dimension makes the multiplicity sets finite, and equality of dimensions identifies those sets. The zero module is handled separately. This criterion compares the two twisted regular modules in the Skolem-Noether argument.
