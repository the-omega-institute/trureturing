# Visible State-Space Dimension

## Abstract

The visible density-state range is compact and convex, with the expected affine dimension bound and complete-observer dimension.

**Theorem 1.1 (The visible state space has the expected affine dimension).**

$$\forall d \in \operatorname{Nat}\left(\right), V \in \operatorname{MatrixOperatorSystem}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{NeZero}\left(d\right) \Rightarrow \left(\operatorname{IsCompact}\left(\operatorname{range}\left(\operatorname{visibleStateReadout}\left(d, V\right)\right)\right) \land \left(\operatorname{ConvexR}\left(\operatorname{range}\left(\operatorname{visibleStateReadout}\left(d, V\right)\right)\right) \land \left(\operatorname{finrankR}\left(\operatorname{direction}\left(\operatorname{affineSpanR}\left(\operatorname{range}\left(\operatorname{visibleStateReadout}\left(d, V\right)\right)\right)\right)\right) \le \operatorname{finrankR}\left(\operatorname{carrier}\left(V\right)\right) - 1 \land \left(\operatorname{Injective}\left(\operatorname{visibleStateReadout}\left(d, V\right)\right) \Rightarrow \operatorname{finrankR}\left(\operatorname{direction}\left(\operatorname{affineSpanR}\left(\operatorname{range}\left(\operatorname{visibleStateReadout}\left(d, V\right)\right)\right)\right)\right) = d^{2} - 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/VisibleStateSpaceDimension.visible_state_space_compact_convex_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The visible state is the canonical trace-pairing readout of density matrices, restricted to the supplied Hermitian operator system.

Density matrices form a compact convex set. A local order-unit perturbation argument identifies the affine directions of their visible image with the readout image of traceless Hermitian directions.

Evaluation at the identity has codimension one and vanishes on those directions, proving the upper bound. Injectivity of the visible readout makes the centered map injective and preserves all d squared minus one traceless degrees of freedom.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/VisibleStateSpaceDimension.visible_state_space_compact_convex_dimension`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Fibers/FutureStatisticsEquivalence](../Fibers/FutureStatisticsEquivalence.md)
- Dependency: [D5/S3/Quantum/Fibers/PhysicalFiber](../Fibers/PhysicalFiber.md)
