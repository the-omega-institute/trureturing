# Relative metric projection stability

## Abstract

A relative operator sandwich controls the change of orthogonal projection onto one subspace.

**Theorem 1.1 (Distance between the two projections).**

Lean statement: `D5/S3/HilbertOperators/RelativeMetricProjectionStability.opNorm_sub_starProjection_le`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/RelativeMetricProjectionStability.opNorm_sub_starProjection_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a bounded symmetric operator on a complex Hilbert space, with l I ≤ A ≤ u I and 0 < l ≤ u. If R fixes the visible subspace V, has range in V, and its residual is A-orthogonal to V, its distance from the ordinary orthogonal projection is at most (u − l)/(2√(ul)). For a unit vector w in V with Rayleigh mean m, positivity of (A − l I)(u I − A) bounds the squared centered residual by (u − m)(m − l). Completing the square bounds the residual divided by m, and orthogonality converts that bound into control of R on the reference orthogonal complement.

**Theorem 1.2 (Change of visible compression).**

Lean statement: `D5/S3/HilbertOperators/RelativeMetricProjectionStability.visibleCompression_sub_le`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/RelativeMetricProjectionStability.visibleCompression_sub_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a bounded operator T, the two compressions agree on the part of T(V) inside V. Their difference factors through the visible-to-hidden block of T. Its norm is bounded by the projection-angle coefficient times the norm of that block.

## References

- Truth anchor: `D5/S3/HilbertOperators/RelativeMetricProjectionStability.opNorm_sub_starProjection_le`
- Truth anchor: `D5/S3/HilbertOperators/RelativeMetricProjectionStability.visibleCompression_sub_le`
- Dependency: [D5/S3/Observer/BlockStructure/FourBlockDecomposition](../Observer/BlockStructure/FourBlockDecomposition.md)
