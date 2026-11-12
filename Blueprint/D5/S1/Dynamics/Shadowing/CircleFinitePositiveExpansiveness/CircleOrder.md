# CircleFinitePositiveExpansiveness - CircleOrder

## Abstract

Two-target accessibility through actual full or proper iterate images on the circle.

**Theorem 1.1 (Connected dense open return chains).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder.return_open_chain_dense`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder.return_open_chain_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nondegenerate overlap of a proper arc and a positive return image propagates through finite-fibre iterates to overlapping arc interiors. Their union is connected and dense: a proper compact closure would trap a nondegenerate arc and contradict the interval obstruction. The return and proper-image assumptions are explicit helper hypotheses, proved when this helper is used in the two-target bridge.

**Theorem 1.2 (A genuine lifted crossing of one of two targets).**

Lean statement: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder.two_target_crossing`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder.two_target_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every continuous finitely positively expansive circle selfmap, every nondegenerate proper arc and any two distinct circle points, some iterate has a continuous real lift whose values on the source segment lie strictly below and strictly above a representative of one target. The full-image case has lifted width at least one and can miss at most one target at a seam. In the proper-image case, late separated images, finite circle packing and nondegenerate overlaps yield the connected dense open return chain. A connected dense circle set cannot omit two points. Interior target membership then gives the actual lifted crossing; density alone is not substituted for crossing.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder.return_open_chain_dense`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/CircleOrder.two_target_crossing`
- Dependency: [D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness/Basic](Basic.md)
