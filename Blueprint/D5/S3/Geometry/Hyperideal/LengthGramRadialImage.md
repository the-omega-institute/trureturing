# Radial Image as a Gram Halfspace Slice

## Abstract

The normalized radial image is exactly the nonnegative coefficient slice cut out by the Gram halfspaces.

The common cut body is defined by nonnegative coefficients, unit total mass, and the four Gram row inequalities. Radial normalization removes the unit-mass scale while preserving the signs. Conversely, a nonzero vector on the unit negative quadric and in these eight coefficient halfspaces has positive total mass; dividing by that mass returns a point of the cut body whose radial image is the original vector.

**Theorem 1.1 (The radial image equals the Gram halfspace slice).**

$$\forall l \in Length6,\; \left(\forall k \in Fin6,\; \operatorname{l}\left(k\right) > 0\right) \Rightarrow \operatorname{image}\left(\operatorname{radial}\left(l\right), \operatorname{cutBody}\left(l\right)\right) = \operatorname{halfspaceSlice}\left(l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramRadialImage.radial_image_halfspace_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse inclusion is constructive: the sum of the nonnegative coordinates is positive because the quadratic value is -1. Normalizing by this sum preserves every Gram inequality and makes the radial denominator exactly the reciprocal of the sum.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramRadialImage.radial_image_halfspace_slice`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramBody](LengthGramBody.md)
