# Projection Commutator Cross-Block Criterion

## Abstract

A canonical orthogonal projection commutes with an operator exactly when both directed cross blocks vanish.

**Theorem 1.1 (A projection commutator is controlled by its two cross blocks).**

$$\forall K, H, V, T,\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(H) \land \operatorname{InnerProductSpace}(K, H) \land\\{}V \in \operatorname{Submodule}(K, H) \land \operatorname{HasOrthogonalProjection}(V) \land T \in \operatorname{ContinuousLinearMap}(K, H, H) \Rightarrow\\{}(\operatorname{commutator}(\operatorname{starProjection}(V), T) = \operatorname{starProjection}(V) \cdot T \cdot \left(1 - \operatorname{starProjection}(V)\right) - \left(1 - \operatorname{starProjection}(V)\right) \cdot T \cdot \operatorname{starProjection}(V) \land (\operatorname{commutator}(\operatorname{starProjection}(V), T) = 0 \iff (\operatorname{starProjection}(V) \cdot T \cdot \left(1 - \operatorname{starProjection}(V)\right) = 0 \land \left(1 - \operatorname{starProjection}(V)\right) \cdot T \cdot \operatorname{starProjection}(V) = 0))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/ProjectionCommutatorCrossBlockCriterion.projection_commutator_cross_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a subspace of a real or complex Hilbert carrier that admits its canonical orthogonal projection P, and set Q to one minus P. For every bounded linear operator T, the commutator of P and T is PTQ minus QTP.

Multiplying a zero commutator by P and Q isolates PTQ; multiplying in the opposite order isolates the negative of QTP. Idempotence and orthogonality of the canonical projection make both diagonal terms disappear. Conversely, two zero cross blocks make their difference zero.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/ProjectionCommutatorCrossBlockCriterion.projection_commutator_cross_blocks`
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](../HiddenFlow/ProjectionCommutatorIdentity.md)
