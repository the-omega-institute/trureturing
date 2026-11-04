# Nonempty strict dual and cap signs

## Abstract

The strict dual/cap Lorentz region contains the realizing barycenter.

At the coefficient barycenter, all inverse-Gram dual pairings are positive and all original-row pairings are negative. The normalized radial lift and the coordinate reconstruction transfer these strict signs to the realizing hyperbolic point.

**Theorem 1.1 (The strict dual/cap region is nonempty).**

$$strictDualCapRegionNonempty$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramStrictRegion.strictDualCapRegion_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof consumes the strict barycenter inequalities from the shared radial body and derives the corresponding strict Lorentz signs.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramStrictRegion.strictDualCapRegion_nonempty`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramDualImage](LengthGramDualImage.md)
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramDualPairing](LengthGramDualPairing.md)
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramMetricSegments](LengthGramMetricSegments.md)
