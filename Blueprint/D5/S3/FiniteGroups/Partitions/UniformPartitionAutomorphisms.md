# Uniform partition automorphisms

## Abstract

The full symmetry group of a uniform partition has unique destination-indexed semidirect coordinates.

For x and y in K times L, the relation is equality of first coordinates. Aut is exactly the existing SuccessorQuotient.relationAut subgroup for this relation: its permutations preserve and reflect the relation. Coordinates use the standard Mathlib SemidirectProduct with a family of permutations of L and a permutation of K. Permutation products compose the right factor first.

**Definition 1.1 (The full partition symmetry subgroup).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; \operatorname{Subgroup}\left(\operatorname{Perm}\left(\operatorname{Product}\left(K, L\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.Aut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subgroup consists of precisely those p for which the first coordinates of p(x) and p(y) are equal if and only if the first coordinates of x and y are equal.

**Definition 1.2 (Relabeling destination fibers).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; \operatorname{MonoidHom}\left(\operatorname{Perm}\left(K\right), \operatorname{MulAut}\left(K \to \operatorname{Perm}\left(L\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.reindex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a block permutation alpha, reindex(alpha)(tau)(w) is tau(alpha inverse(w)). This is Mathlib's multiplicative arrow congruence, with its homomorphism law checked pointwise.

**Definition 1.3 (The standard semidirect product).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; \operatorname{Coordinates}\left(K, L\right) = \operatorname{SemidirectProduct}\left(K \to \operatorname{Perm}\left(L\right), \operatorname{Perm}\left(K\right), \operatorname{reindex}\left(K, L\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.Coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Writing coordinates as (sigma,alpha), their product with (tau,beta) is (eta,alpha beta), where eta(w)=sigma(w) tau(alpha inverse(w)). This is the natural action on the block index set; it is not a regular action on the whole block permutation group.

**Definition 1.4 (Action of the coordinates).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; \left(K \to \operatorname{Perm}\left(L\right)\right) \to \left(\operatorname{Perm}\left(K\right) \to \operatorname{Aut}\left(K, L\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.assemble` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

assemble(s,a) sends (v,t) to (a(v),s(a(v))(t)). It is built with prodCongr followed by prodCongrRight; injectivity of a proves preservation and reflection of the partition relation.

**Definition 1.5 (Unique explicit coordinates).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; \operatorname{Nonempty}\left(L\right) \Rightarrow \operatorname{Equiv}\left(\operatorname{Aut}\left(K, L\right), \operatorname{Coordinates}\left(K, L\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose any t in the nonempty fiber type. For p in Aut, alpha(v) is the first coordinate of p(v,t). Relation preservation makes this independent of the fiber coordinate; reflection makes alpha injective, and preimages of (w,t) make it onto. At destination w, sigma(w)(t) is the second coordinate of p(alpha inverse(w),t). Injectivity and surjectivity of p prove that every sigma(w) is a permutation. Assembly and extraction are inverse in both directions. Consequently both alpha and sigma are unique, including for empty K and singleton L. Empty L is excluded: if K has multiple permutations, the action on an empty product cannot determine alpha.

**Definition 1.6 (The full symmetry group isomorphism).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; \operatorname{Nonempty}\left(L\right) \Rightarrow \operatorname{MulEquiv}\left(\operatorname{Aut}\left(K, L\right), \operatorname{Coordinates}\left(K, L\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.automorphismEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate equivalence is multiplicative. Composing two assembled actions gives precisely eta(w)=sigma(w) tau(alpha inverse(w)); the inverse-index cancellation is verified in Lean. No centralizer or cyclic ordering is imposed.

**Theorem 1.7 (Exact finite group order).**

$$\forall K \in Typeu,\; \forall L \in Typev,\; \left(\operatorname{Finite}\left(K\right) \land \left(\operatorname{Finite}\left(L\right) \land \operatorname{Nonempty}\left(L\right)\right)\right) \Rightarrow \operatorname{card}\left(\operatorname{Aut}\left(K, L\right)\right) = \operatorname{power}\left(\operatorname{factorial}\left(\operatorname{card}\left(L\right)\right), \operatorname{card}\left(K\right)\right) \cdot \operatorname{factorial}\left(\operatorname{card}\left(K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.card_aut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proved coordinate equivalence identifies the carrier with (K to Perm L) times Perm K. Mathlib's permutation cardinality and function cardinality then give the factorial formula. The empty block-index set gives order one, and singleton fibers give the full permutation group on K.

This construction supplies the full uniform-block symmetry structure needed after reconstructing a partition from its saturated subsets. FinitePartitionAlgebraAntiequivalence already provides that reconstruction; MersenneDifferenceZeroSubsets already relates physical zero subsets to rotational invariance. Transport through an arithmetic gcd-residue chart remains a separate obligation. A rotation centralizer retains cyclic order inside each orbit, which saturated subsets do not observe. For orbit lengths three on two blocks the full order is 72, while the rotation centralizer has order 18. For orbit lengths two on three blocks the full order is 48; a regular wreath product indexed by all six block permutations would instead have order 384. These comparisons explain the structural distinction; this module proves the generic classification and does not claim the arithmetic transport or literature novelty.

## References

- Truth anchor: `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.Aut`
- Truth anchor: `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.Coordinates`
- Truth anchor: `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.assemble`
- Truth anchor: `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.automorphismEquiv`
- Truth anchor: `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.card_aut`
- Truth anchor: `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.coordinates`
- Truth anchor: `D5/S3/FiniteGroups/Partitions/UniformPartitionAutomorphisms.reindex`
- Dependency: [D5/S3/FiniteGroups/SuccessorQuotient](../SuccessorQuotient.md)
