# A linear nonpositive bound is preserved by convexification

## Abstract

A linear support inequality on generators extends across their convex hull.

Let s be a set of points in the four-coordinate real space and let L be a real linear functional. If L is nonpositive at every generator in s, then it is nonpositive at every point of the convex hull of s.

**Theorem 1.1 (Linear support inequalities survive convexification).**

$$linearNonposOnHull$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LinearNonposOnHull.linear_nonpos_on_hull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The convex hull is the smallest convex set containing the generators. Linearity evaluates a two-point convex combination as the corresponding weighted sum, and nonnegative weights preserve the nonpositive bounds.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LinearNonposOnHull.linear_nonpos_on_hull`
