# Record Classicality Fixed Point

## Abstract

Unread record fixed points are exactly the matrices with no cross-record blocks.

**Theorem 1.1 (Record classicality is the unread fixed-point condition).**

$$\forall n, K, \operatorname{Fintype}\left(n\right), \operatorname{Fintype}\left(K\right),\\{}\forall P: K \to M_{n}(\mathbb{C}), rho\in M_{n}(\mathbb{C}),\\{}\operatorname{Record}\left(P\right) \Rightarrow U_{P}(rho) = rho \Leftrightarrow \forall k, l\in K, k \neq l \Rightarrow P_{k} rho P_{l} = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/RecordClassicalityFixedPoint.record_classicality_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a finite complete family of pairwise orthogonal, self-adjoint idempotent complex projections. The unread record map sums the diagonal compressions P_k rho P_k.

The formal theorem directly applies the canonical unread-state fixed-point characterization. It retains both directions: a fixed matrix has every cross-record block equal to zero, and vanishing cross-record blocks reconstruct the fixed matrix by projection completeness.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/RecordClassicalityFixedPoint.record_classicality_fixed_point`
- Dependency: [D5/S3/Observer/Conditioning](../Conditioning.md)
