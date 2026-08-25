# Four-Block Decomposition

## Abstract

An operator splits into four blocks with visible and residual domain-codomain types.

**Theorem 1.1 (An operator is the sum of its four projection blocks).**

$$\forall A, [\operatorname{Ring}\left(A\right)], \forall P, Q, T \in A, Q = 1 - P \Rightarrow T = P \cdot T \cdot P + P \cdot T \cdot Q + Q \cdot T \cdot P + Q \cdot T \cdot Q.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/FourBlockDecomposition.four_block_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any possibly noncommutative ring, let Q equal one minus P. Inserting P plus Q on both sides of T expands T into PTP, PTQ, QTP, and QTQ.

The identity needs neither idempotence nor a nontrivial carrier. It includes zero dynamics, identity dynamics, P equal to zero or one, and empty-index matrix rings.

**Theorem 1.2 (The complement relation cannot be omitted).**

$$P = 0, Q = 0, T = 1 \in \mathbb{Z}, Q \neq 1 - P \land T \neq P \cdot T \cdot P + P \cdot T \cdot Q + Q \cdot T \cdot P + Q \cdot T \cdot Q.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/FourBlockDecomposition.complement_relation_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the integers, take P and Q to be zero and T to be one. Then Q is not one minus P, and every proposed block is zero, so their sum is not T.

**Theorem 1.3 (The four typed blocks realize the ambient projection products).**

$$PTP: V \to V,\ PTQ: V^{\perp} \to V,\ QTP: V \to V^{\perp},\ QTQ: V^{\perp} \to V^{\perp}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/FourBlockDecomposition.typed_block_formulas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a subspace V admitting orthogonal projection, the four bundled continuous linear maps have types V to V, V-perp to V, V to V-perp, and V-perp to V-perp.

After coercion into the ambient space, their values are exactly PTP, PTQ, QTP, and QTQ. The domain and codomain claims are therefore checked by Lean's types rather than recorded only in prose.

**Theorem 1.4 (Orthogonal projection gives the typed four-block decomposition).**

$$[\operatorname{HasOrthogonalProjection}\left(V\right)], Q = 1 - P \Rightarrow T = P \cdot T \cdot P + P \cdot T \cdot Q + Q \cdot T \cdot P + Q \cdot T \cdot Q.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/FourBlockDecomposition.orthogonal_four_block_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projections onto V and its orthogonal complement sum to the identity. Splitting both the input and each output of T gives the four ambient projection products.

Only the HasOrthogonalProjection instance is assumed. Completeness of the ambient space and a separate closedness hypothesis are not needed.

**Lemma 1.5 (The commutator is the off-diagonal corollary).**

$$Q = 1 - P \Rightarrow P \cdot T - T \cdot P = P \cdot T \cdot Q - Q \cdot T \cdot P.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/FourBlockDecomposition.commutator_off_diagonal_corollary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With Q equal to one minus P, the commutator of P and T is PTQ minus QTP. The Lean proof directly invokes the existing adjacent commutator theorem rather than constructing a second proof.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/FourBlockDecomposition.commutator_off_diagonal_corollary`
- Truth anchor: `D5/S3/Observer/BlockStructure/FourBlockDecomposition.complement_relation_is_necessary`
- Truth anchor: `D5/S3/Observer/BlockStructure/FourBlockDecomposition.four_block_decomposition`
- Truth anchor: `D5/S3/Observer/BlockStructure/FourBlockDecomposition.orthogonal_four_block_decomposition`
- Truth anchor: `D5/S3/Observer/BlockStructure/FourBlockDecomposition.typed_block_formulas`
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](../HiddenFlow/ProjectionCommutatorIdentity.md)
