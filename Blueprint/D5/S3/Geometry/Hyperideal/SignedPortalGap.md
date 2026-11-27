# SignedPortalGap

## Abstract

Minimizing crossing count can give arbitrarily poor path length in six signed cyclic sheets.

**Theorem 1.1 (An unbounded signed-portal detour).**

Lean statement: `D5/S3/Geometry/Hyperideal/SignedPortalGap.finite_signed_shift_unbounded_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SignedPortalGap.finite_signed_shift_unbounded_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive L, each of six sheets is a path on L+1 vertices. Reciprocal near portals of offsets zero and one give a three-crossing route at the starting base cell. The direct offset-two portal is available only at the far end, so an exactly one-crossing route costs 2L+1; the unconstrained optimum is exactly three.

The theorem concerns a finite signed graph family. It does not assert that its members are tetrahedral manifold caps, have minimum edge degree seven, or satisfy hyperbolic angle equations. The internal shortest-distance overlay argument is classical.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SignedPortalGap.finite_signed_shift_unbounded_gap`
