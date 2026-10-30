# Nondegeneracy of the twenty original coefficient cells

## Abstract

For every strictly positive six-length vector, each of the twenty original four-point coefficient cells is an affine simplex.

The result uses the literal facet and ridge support table, so it preserves the original endpoint order and does not add a Gram-determinant or geometric-realization hypothesis.

**Theorem 1.1 (All twenty cells are affinely independent).**

$$verticesAffineIndependent$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramCellNondegeneracy.vertices_affine_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first support is the entry facet n. It is strictly nonzero at the barycenter and vanishes at the three ordered endpoint entries. The second support is ridge n; it is nonzero at the first endpoint and vanishes at the last two. The generic support-triangularization lemma then reduces an affine relation to a scalar multiple of the difference of the final two endpoints. The endpoint classification proves that those two ordered endpoints are distinct for every one of the twenty rows.

This theorem supplies only cell nondegeneracy. It does not assert that the twenty cells cover the cut body, describe all pairwise intersections, or identify their geometric images with hyperbolic tetrahedra; those are separate claims.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramCellNondegeneracy.vertices_affine_independent`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramSideTrace](LengthGramSideTrace.md)
- Dependency: [D5/S3/Geometry/Hyperideal/SupportAffineIndependent](SupportAffineIndependent.md)
