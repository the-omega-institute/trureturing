# Recover the full scalar boundary state sum of a signed ribbon bouquet

## Abstract

Recover the full scalar boundary state sum of a signed ribbon bouquet.

**Theorem 1.1 (Recover the full scalar boundary state sum of a signed ribbon bouquet).**

$$\forall R \in \operatorname{ValidSignedRibbonBouquets}\left(\right),\; \forall d \in \operatorname{NonzeroReals}\left(\right),\; \forall w \in \operatorname{RealSmoothingWeights}\left(R\right),\; \operatorname{PhysicalQuotientMomentWalsh}\left(R, d, w\right) = \operatorname{LiteralBoundaryStateSum}\left(R, d, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/SignedBouquetMomentReconstruction.literal_intrinsic_signed_bouquet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The labels are intrinsic: quotient the binary chord space by the radical of the signed pairing, and take the images of the chord basis. The retained form rank is a function of the retained column span, and the quotient-code trace moments recover its loop weight. Walsh inversion yields the weighted literal four-flag boundary state sum for any nonzero real loop value and arbitrary smoothing weights, including zero. There is no genus bound and no separately supplied label table. This is a one-vertex theorem, not the writhe-normalized Jones invariant or a multi-vertex reconstruction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/SignedBouquetMomentReconstruction.literal_intrinsic_signed_bouquet`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/SignedBouquetBoundary](../../../Combinatorics/PerfectMatchings/SignedBouquetBoundary.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/ProjectionMoments](ProjectionMoments.md)
