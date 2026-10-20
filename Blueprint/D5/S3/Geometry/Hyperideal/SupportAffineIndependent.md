# Affine independence from two support traces

## Abstract

Two independent support traces and a separating pair force four points to be affinely independent.

Let four points v0 through v3 lie in the four-coordinate real space. Suppose a linear support is nonzero at v0 and zero at the other three points, while a second support is nonzero at v1 and zero at v2 and v3. If v2 and v3 are distinct, then the four points are affinely independent.

**Theorem 1.1 (Two support traces triangularize affine relations).**

$$supportAffineIndependent$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SupportAffineIndependent.support_affine_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An affine relation has coefficient sum zero and weighted vector sum zero. Applying the first support forces the coefficient at v0 to vanish; applying the second forces the coefficient at v1 to vanish. The sum-zero equation then makes the last two coefficients opposite, and the vector relation reduces to a scalar multiple of v2-v3. Their distinctness forces that scalar to vanish as well.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SupportAffineIndependent.support_affine_independent`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramPolytope](LengthGramPolytope.md)
