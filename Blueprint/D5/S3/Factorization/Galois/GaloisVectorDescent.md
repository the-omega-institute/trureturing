# Effective descent for semilinear Galois vector spaces.

## Abstract

Effective descent for semilinear Galois vector spaces.

The invariant-generation method follows Qiuzhen-CFSG/CFSG, Theory/Representation/FiniteFieldSemilinearDisplacement/Descent.lean, revision 0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7, Apache-2.0. The formulation with independent group, base-field, extension-field and carrier universes and the canonical tensor equivalence are the formal integration here. Basis extraction and base change use Mathlib. This is classical semilinear descent, with no claim of a new descent theorem.

**Theorem 1.1 (span fixedPoints).**

$$\forall G \in Type*,\; \forall K \in Type*,\; \forall L \in Type*,\; \forall V \in Type*,\; [Group\left(G\right)], [Finite\left(G\right)], [Field\left(K\right)], [Field\left(L\right)], [Algebra\left(K, L\right)], [MulSemiringAction\left(G, L\right)], [IsGaloisGroup\left(G, K, L\right)], [AddCommGroup\left(V\right)], [Module\left(L, V\right)], [DistribMulAction\left(G, V\right)], [SMulDistribClass\left(G, L, V\right)], \operatorname{Submodule}.\operatorname{span}\left(L, \operatorname{MulAction}.\operatorname{fixedPoints}\left(G, V\right)\right) = \operatorname{Top}.\operatorname{top}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GaloisVectorDescent.span_fixedPoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed vectors span over the extension field. Twisted orbit sums are fixed, so a linear form vanishing on the fixed vectors gives a relation among distinct field automorphisms. Artin independence makes that form zero. No division by the group order or finite-dimensionality is required.

**Theorem 1.2 (exists invariant basis).**

$$\forall G \in Type*,\; \forall K \in Type*,\; \forall L \in Type*,\; \forall V \in Type*,\; [Group\left(G\right)], [Finite\left(G\right)], [Field\left(K\right)], [Field\left(L\right)], [Algebra\left(K, L\right)], [MulSemiringAction\left(G, L\right)], [IsGaloisGroup\left(G, K, L\right)], [AddCommGroup\left(V\right)], [Module\left(L, V\right)], [DistribMulAction\left(G, V\right)], [SMulDistribClass\left(G, L, V\right)], \exists iota \in Type*,\; \exists b \in Basis\left(iota, L, V\right),\; \forall g \in G,\; \forall i \in iota,\; \operatorname{HSMul}.\operatorname{hSMul}\left(g, b\left(i\right)\right) = b\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GaloisVectorDescent.exists_invariant_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extracting a basis from the spanning fixed vectors gives a basis fixed pointwise by the group; its index type lies in the carrier universe.

$\forall G \in Type*,\; \forall K \in Type*,\; \forall L \in Type*,\; \forall V \in Type*,\; [Group\left(G\right)], [Finite\left(G\right)], [Field\left(K\right)], [Field\left(L\right)], [Algebra\left(K, L\right)], [MulSemiringAction\left(G, L\right)], [IsGaloisGroup\left(G, K, L\right)], [AddCommGroup\left(V\right)], [Module\left(L, V\right)], [DistribMulAction\left(G, V\right)], [SMulDistribClass\left(G, L, V\right)], [Module\left(K, V\right)], [IsScalarTower\left(K, L, V\right)], \operatorname{GaloisVectorDescent}.\operatorname{descentEquiv}\left(G, K, L, V\right):LinearEquiv\left(\operatorname{RingHom}.\operatorname{id}\left(L\right), \operatorname{Algebra}.\operatorname{TensorProduct}\left(K, L, \operatorname{GaloisVectorDescent}.\operatorname{fixedSubmodule}\left(G, K, L, V\right)\right), V\right), \forall a \in L,\; \forall w \in \operatorname{GaloisVectorDescent}.\operatorname{fixedSubmodule}\left(G, K, L, V\right),\; \operatorname{GaloisVectorDescent}.\operatorname{descentEquiv}\left(G, K, L, V, \operatorname{TensorProduct}.\operatorname{tmul}\left(a, w\right)\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(a, \operatorname{Subtype}.\operatorname{val}\left(w\right)\right)$

The canonical L-linear equivalence descentEquiv sends a tensor a tensor w to a times w. Its inverse is determined by the invariant basis. The K-module and scalar-tower structures in this formula are scalar restriction; they impose no new restriction on an L-vector space.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GaloisVectorDescent.exists_invariant_basis`
- Truth anchor: `D5/S3/Factorization/Galois/GaloisVectorDescent.span_fixedPoints`
