# IntervalObstruction - Basic

## Abstract

Strict all-time forward Bowen bounds, exact interval pullbacks and monotone trapping.

**Definition 1.1 (Strict forward Bowen sets).**

Lean statement: `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.ForwardBowen`

*Formalization.* `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.ForwardBowen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ForwardBowen f epsilon x contains precisely those y for which dist(f^t(x), f^t(y)) < epsilon at every natural t, including zero. ForwardBowenBound uses encard, so an infinite set cannot satisfy a finite bound. FinitelyPositiveExpansive chooses one epsilon > 0 and one natural N >= 1 before every center.

**Theorem 1.2 (Exact selected interval pullbacks).**

Lean statement: `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.exact_pullback`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.exact_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous map on a nondegenerate closed real interval has a selected nondegenerate closed subinterval mapping exactly onto each nondegenerate closed target interval contained in its image. The proof selects the first upper-level hit and the last lower-level hit; it does not identify the entire inverse image with an interval.

**Theorem 1.3 (All-time small intervals for monotone dynamics).**

Lean statement: `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.strictly_monotone_small_segment`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.strictly_monotone_small_segment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a continuous strictly increasing or strictly decreasing interval self-map, every positive requested scale admits a nondegenerate subinterval whose images have smaller diameter at every forward time. Monotone bounded orbits have vanishing successive gaps; the decreasing-map case uses the square and controls all odd times by compact uniform continuity. These constructions are used by the obstruction and its return-chain argument.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.ForwardBowen`
- Truth anchor: `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.exact_pullback`
- Truth anchor: `D5/S1/Dynamics/Shadowing/IntervalObstruction/Basic.strictly_monotone_small_segment`
- Dependency: [D5/S1/Dynamics/Shadowing/UniformTracing](../UniformTracing.md)
