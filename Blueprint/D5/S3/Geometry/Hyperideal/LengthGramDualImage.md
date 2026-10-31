# Dual and cap sign characterization of the realizing range

## Abstract

The realizing hyperbolic range is exactly the dual/cap Lorentz sign region.

For a realizing row matrix M, the inverse-Gram dual vectors read off the four coefficient coordinates, while pairing with the original rows reads off the four Gram inequalities. The determinant identity makes M invertible, so every hyperbolic lift satisfying these eight signs has a unique coefficient vector. The normalized radial image theorem then puts that vector back in the cut body and reconstructs the point.

**Theorem 1.1 (The range equals the dual/cap sign region).**

$$rangeEqDualCapRegion$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramDualImage.range_eq_dualCapRegion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward direction uses the exact lift of the coordinate witness. For the reverse direction, the inverse matrix recovers coefficients from an arbitrary lift; the negative unit quadratic and the two sign families are then precisely the hypotheses of the radial image theorem.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramDualImage.range_eq_dualCapRegion`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramDualPairing](LengthGramDualPairing.md)
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramMetricSegments](LengthGramMetricSegments.md)
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramRadialImage](LengthGramRadialImage.md)
- Dependency: [D5/S3/Geometry/Hyperideal/LorentzGramDeterminant](LorentzGramDeterminant.md)
