# The five physical code moments and literal ribbon boundaries

## Abstract

An exact scalar ribbon boundary sum from five diagonal density-moment readouts.

**Theorem 1.1 (Actual ribbon boundary sum at a real Kauffman parameter).**

$$\forall R \in \operatorname{ValidOrientedRibbonBouquets}\left(\right),\; \forall ell \in \operatorname{BinaryPairingTables}\left(R\right),\; \forall weights \in \operatorname{RealSmoothingWeights}\left(R\right),\; \forall A \in \operatorname{PositiveReals}\left(\right),\; \operatorname{ScaledFiveCodeWalsh}\left(R, ell, weights, A\right) = \operatorname{LiteralBoundaryStateSum}\left(R, weights, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalRibbonBoundaryWalsh.actual_bouquet_bracket_walsh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an oriented one-vertex ribbon the interlacing table is given by the standard alternating pairing on two binary coordinates per chord. Fix genuine retained-band switches and give two arbitrary real smoothing weights per edge. The five encoders retain no coordinate, one of the three line quotients, or both coordinates. Each readout is the trace moment of a normalized complex diagonal density on the selected sites.

Write d for the negative sum of the square and inverse square of the positive real Kauffman parameter, and q for d squared. In these conventions q is at least four. The five coefficients are minus two, q, q, q, and minus two q, all divided by q minus two. The signed combination cancels the label dimensions not seen by the restricted pairing. Weighted Walsh inversion then recovers the literal boundary-circle state sum; no local smoothing weight is inverted.

This theorem derives each boundary count from its actual retained-dart permutation. The result is the unnormalized scalar state sum, not the writhe-normalized Jones invariant or a classification of knots or links. A valid two-coordinate pairing table is required, and arbitrary multi-vertex ribbons are not yet covered.

**Theorem 1.2 (Exact full-pair physical readout).**

$$\forall K \in \operatorname{PositiveOrdersWithBaseNotTwo}\left(\right),\; \operatorname{PhysicalFullPairReadout}\left(K\right) = \operatorname{Inverse}\left(\operatorname{Pow}\left(2, \operatorname{Sub}\left(K, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalRibbonBoundaryWalsh.physical_full_pair_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the two standard binary coordinate vectors, with the three distinct line projections, full label and zero label. These five actual readouts mix to the reciprocal entropy base whenever the order is positive and that base differs from two.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalRibbonBoundaryWalsh.actual_bouquet_bracket_walsh`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalRibbonBoundaryWalsh.physical_full_pair_readout`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/RibbonCohomologyRank](../../../Combinatorics/PerfectMatchings/RibbonCohomologyRank.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments](DiagonalLinearCodeMoments.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh](GraphStateSmallOrderWalsh.md)
