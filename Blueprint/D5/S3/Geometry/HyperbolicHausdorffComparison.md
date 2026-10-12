# Hyperbolic Hausdorff comparison

## Abstract

Local Hausdorff comparison for the native hyperbolic three-space metric.

The coordinate type carries its Euclidean subtype metric; the same points in HyperbolicThreeSpace carry the frozen curvature-minus-one arsinh metric. For a coordinate ball of radius r below its centre height h, the two distances satisfy D ≤ (h+2r)d and d ≤ D/(h-r). Applying the pinned Hausdorff image inequalities in both directions gives a local measure comparison for every subset. The scalar lower estimate follows from x/(1+x) ≤ log(1+x) ≤ arsinh(x), and the upper estimate follows from t ≤ sinh(t) for t ≥ 0.

**Theorem 1.1 (Two-sided local measure comparison).**

$$\forall p \in U,\; \forall r \in Real,\; (0 < r) \implies ((r < \operatorname{height}\left(p\right)) \implies (\forall s \in \operatorname{Set}\left(U\right),\; (\operatorname{Subset}\left(s, \operatorname{ball}\left(p, r\right)\right)) \implies (\operatorname{hausdorffMeasure}\left(3, s\right) \le (\operatorname{ofReal}\left(\operatorname{height}\left(p\right) + 2 \cdot r\right))^{3} \cdot \operatorname{hausdorffMeasure}\left(3, \operatorname{image}\left(\operatorname{HyperbolicSpace.mk}, s\right)\right) \land \operatorname{hausdorffMeasure}\left(3, \operatorname{image}\left(\operatorname{HyperbolicSpace.mk}, s\right)\right) \le (\operatorname{ofReal}\left(\operatorname{inv}\left(\operatorname{height}\left(p\right) - r\right)\right))^{3} \cdot \operatorname{hausdorffMeasure}\left(3, s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/HyperbolicHausdorffComparison.local_hausdorff_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is UpperHalfSpace over the complex numbers, h=height(p), H3 is Mathlib's raw three-dimensional Hausdorff measure on the indicated metric type, and lift is the existing HyperbolicSpace constructor. Empty sets, nonmeasurable subsets and coincident points are included. The result uses Mathlib.MeasureTheory.Measure.Hausdorff at the project's pinned revision. This is a formal synthesis of standard distance and Hausdorff estimates, with no literature novelty claim.

This supplies local metric-measure distortion on the same native model used by LengthGramBody.shared_radial_body. It does not identify normalized volume: Euclidean Haar normalization, the exact height^-3 density, the Jacobian of the original three-affine-coordinate Gram body image, frame independence, positivity and finiteness, and the finite strictly positive flat-boundary limit remain separate obligations. The original positive six-length and all-six strict cosine domain is unchanged. The tensor/path-distance calibration described in the owning Library note is also not asserted by this comparison.

## References

- Truth anchor: `D5/S3/Geometry/HyperbolicHausdorffComparison.local_hausdorff_comparison`
- Dependency: [D5/S3/Geometry/HyperbolicUpperHalfSpace](HyperbolicUpperHalfSpace.md)
