# Flat hyperbolic vertex edge inequality

## Abstract

A flat hyperbolic face angle forces the opposite truncated edge to be longest.

For positive real side lengths a, b and c, define the hyperbolic cosine-law quantity (cosh(a) cosh(b) - cosh(c)) / (sinh(a) sinh(b)). If this quantity is at most -1, then a+b is at most c. This is the reusable analytic core of the flat-vertex longest-edge argument; it does not construct the surrounding hyperideal face, identify an arcosh truncation, or prove the global CFMP geometry.

**Definition 1.1 (Hyperbolic face cosine-law quantity).**

Lean statement: `D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge.faceCosine`

*Formalization.* `D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge.faceCosine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient of cosh(a) cosh(b) - cosh(c) by the positive denominator sinh(a) sinh(b).

**Theorem 1.2 (Flat angle makes the opposite side longest).**

Lean statement: `D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge.flat_vertex_longest_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge.flat_vertex_longest_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a, b and c, the hypothesis faceCosine(a,b,c) <= -1 implies a+b <= c. The proof uses positivity of sinh on positive inputs, the addition formula for cosh, and injectivity of cosh on nonnegative reals.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge.faceCosine`
- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatVertexLongestEdge.flat_vertex_longest_edge`
