# Exterior Realization of the Infinite Ghost Carrier

## Abstract

Signed-subset creation and deletion are the coordinates of actual exterior multiplication and contraction.

For any commutative ring K, let V be the free K-module with basis e_i indexed by all natural numbers. Fock(K) consists of finite K-linear combinations of finite subsets S of the natural numbers. E is the linear equivalence taking the coordinate vector at S to the product of the exterior generators e_i in increasing order. Its existence uses Mathlib's exterior-algebra basis and its representation equivalence, including the empty product and the zero ring.

Creation inserts i when it is absent and is zero otherwise. Deletion erases i when it is present and is zero otherwise. Both operations carry the factor (-1) raised to the number of elements of S smaller than i. The one-particle coordinate functional epsilon_i evaluates a vector at i; delta_i denotes Mathlib's left contraction by epsilon_i.

**Theorem 1.1 (Signed creation intertwines exterior multiplication).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall i\in \mathbb{N}, \forall v\in \operatorname{Fock}\left(K\right),\ \operatorname{E}\left(K, \operatorname{create}\left(i, v\right)\right)=\operatorname{iota}\left(K, \operatorname{e}\left(i\right)\right) \operatorname{E}\left(K, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostExteriorOperators.exterior_create` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring K, natural i and state v, E(create(i)v) equals iota_K(e_i) * E(v), i.e. E(v) left-multiplied by iota_K(e_i). Induction by the least element of a subset computes the insertion parity. Passing a generator across the least element uses the exterior anticommutation identity; repeated generators have square zero.

**Theorem 1.2 (Signed deletion intertwines actual contraction).**

$$\forall K:Type, [\operatorname{CommRing}\left(K\right)], \forall i\in \mathbb{N}, \forall v\in \operatorname{Fock}\left(K\right),\ \operatorname{E}\left(K, \operatorname{annihilate}\left(i, v\right)\right)=\operatorname{delta}\left(K, i, \operatorname{E}\left(K, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostExteriorOperators.exterior_annihilate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring K, natural i and state v, E(annihilate(i)v) equals delta_i(E(v)). The contraction recurrence delta_i(iota(e_a)x)=epsilon_i(e_a)x-iota(e_a)delta_i(x) computes the deletion sign, and linearity extends it to every finite superposition. Consequently the actual signed operators inherit Mathlib's CAR and supply the ghost stress-current commutators on the same carrier.

These are exact algebraic coordinates on an infinite mode set. No finite truncation, characteristic-zero hypothesis or positive inner product is used. The result concerns fermionic operators; it does not establish Virasoro central charge, BRST cohomology, string amplitudes or spacetime dynamics.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostExteriorOperators.exterior_annihilate`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostExteriorOperators.exterior_create`
- Dependency: [D5/S3/VertexAlgebra/BcGhostFockSupport](BcGhostFockSupport.md)
