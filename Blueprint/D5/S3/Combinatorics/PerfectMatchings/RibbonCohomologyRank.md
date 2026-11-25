# Boundary cochains and binary interlacement

## Abstract

Exact binary rank from literal boundary cycles of a one-vertex orientable ribbon.

**Theorem 1.1 (Literal boundary circles plus interlacement rank).**

$$\forall R \in \operatorname{ValidOrientedBouquetSwitches}\left(\right),\; \operatorname{Add}\left(\operatorname{BoundaryCircles}\left(R\right), \operatorname{BinaryInterlacementRank}\left(R\right)\right) = \operatorname{Add}\left(1, \operatorname{RetainedChords}\left(R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/RibbonCohomologyRank.literal_bouquet_boundary_interlace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the one-circular-order form of the classical Cohn–Lempel equality (Journal of Combinatorial Theory A 13 (1972), 83–89, DOI 10.1016/0097-3165(72)90010-6). The inputs are an oriented cyclic dart order and an involution transposing precisely the selected disjoint pairs, while all unselected darts remain on the carrier as fixed points of the pairing.

A field-valued function constant on boundary cycles is determined by its value at the initial dart and its oriented chord-endpoint differences. Each chord contributes two opposite increments; cyclic integration cancels them. Summing from the lower endpoint to the upper endpoint retains its own difference and the differences of exactly the interlacing chords. In characteristic two the orientation signs agree. The free initial value and the kernel of the actual interlacement map therefore count the boundary cycles.

This is not a surface homology construction or a statement about arbitrary multi-vertex ribbon graphs; it is the literal one-vertex permutation count, with the boundary circles obtained without assuming an Euler formula.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/RibbonCohomologyRank.literal_bouquet_boundary_interlace`
