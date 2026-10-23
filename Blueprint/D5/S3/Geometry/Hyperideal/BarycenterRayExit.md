# Barycenter support-ratio exit

## Abstract

Every non-barycentric point of the common cut body reaches an original support trace.

For six positive lengths, let C be the common nonnegative unit-sum cut body defined by the six-length Gram rows. From any point x in C other than the barycenter, the ray from the barycenter can be extended by a positive ratio t no larger than one until it reaches one of the eight original coordinate or Gram support traces.

**Theorem 1.1 (A barycentric ray reaches an original boundary support).**

$$barycenterRayExit$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/BarycenterRayExit.barycenter_ray_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof first finds a coordinate below one quarter, then applies the finite support-ratio exit lemma to all four coordinate supports and four Gram supports. The rescaled endpoint keeps the simplex and Gram inequalities, and the maximizing support is exactly zero. No subdivision coverage or disjointness claim is included here.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/BarycenterRayExit.barycenter_ray_exit`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramPolytope](LengthGramPolytope.md)
- Dependency: [D5/S3/Geometry/Hyperideal/SupportRatioExit](SupportRatioExit.md)
