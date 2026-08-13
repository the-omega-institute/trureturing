# Three-Cycle Fixed-Point Gap

## Abstract

The three-state successor cycle has distinct least and greatest fixed points.

**Theorem 1.1 (Least and greatest cycle solutions differ).**

$$\operatorname{lfp}(threeCycleOperator) \neq \operatorname{gfp}(threeCycleOperator)$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/ThreeCycleGap.three_cycle_has_fixed_point_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen three-cycle theorem identifies the least fixed point with the empty set and the greatest fixed point with the full carrier. The explicit first state belongs to the latter and not the former, so the two fixed points are distinct.

Pinned Mathlib supplies the extremal fixed-point construction, while the repository supplies this concrete successor-cycle instance. No existing declaration states the resulting inequality.

This continuation closes only the concrete self-reference gap. The separate induction and coinduction reachability interpretation remains outside this declaration.

## References

- Truth anchor: `D5/S1/FixedPoints/ThreeCycleGap.three_cycle_has_fixed_point_gap`
- Dependency: [D5/S1/Dynamics/KnasterTarski](../Dynamics/KnasterTarski.md)
