# Gauss Infinite Fiber

## Abstract

Every interior value of the real Gauss map has infinitely many inverse branches.

**Theorem 1.1 (Every interior Gauss fiber is infinite).**

$$\forall y\in (0,1),\ \operatorname{Infinite}(\{x\in (0,1) \mid \operatorname{fract}(\frac{1}{x})=y\})$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/GaussInfiniteFiber.gauss_map_interior_fiber_infinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix y strictly between zero and one. For each natural n, the point x_n=1/(n+1+y) lies in the open unit interval. Taking the reciprocal and then the fractional part returns y.

The branch points are pairwise distinct because inversion and the natural-to-real embedding are injective. Mathlib's infinite-range theorem therefore makes their containing Gauss fiber infinite.

This closes only the infinitely-many-inverse-branches clause of residual appendix/E.124. It does not assert invertibility of the natural extension, an invariant measure, or any restart dynamics.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/GaussInfiniteFiber.gauss_map_interior_fiber_infinite`
