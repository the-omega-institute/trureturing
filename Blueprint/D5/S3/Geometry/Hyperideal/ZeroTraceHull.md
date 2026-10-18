# Convex hull of a common supporting trace

## Abstract

A finite convex hull meets a family of nonpositive supports at the hull of its zero-support vertices.

Let s be a set of points in the four-coordinate real space and let L be a family of linear supports. Assume every generator is in every nonpositive support halfspace. The points of the convex hull on the common zero trace are exactly the convex hull of those generators that already lie on every zero trace.

**Theorem 1.1 (A common zero trace commutes with convex hull).**

$$zeroTraceHull$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ZeroTraceHull.zero_trace_hull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward inclusion follows from convexity of the hull and linearity of each support. For the reverse inclusion, write a point of the hull as a finite convex combination. Each summand is nonpositive, while the weighted sum is zero, so every nonzero-weight summand has zero support. Filtering out zero weights preserves both the total weight and the represented point.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/ZeroTraceHull.zero_trace_hull`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramPolytope](LengthGramPolytope.md)
