# Forward separation of immersed short arcs

## Abstract

Forward separation of immersed short arcs

**Theorem 1.1 (Short paths immersed by every iterate have a uniform separation scale).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteGraphBowenArcs.separates_points_of_immersed_paths`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteGraphBowenArcs.separates_points_of_immersed_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As long as the endpoints of a short immersed arc stay close, continuity keeps the next image in an edge interval or small vertex star. There the image diameter is the distance between its endpoints. With no separating time the entire nondegenerate arc would remain in a single forward Bowen ball, contradicting its finite cardinal bound.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteGraphBowenArcs.separates_points_of_immersed_paths`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphSmallArcs](FiniteGraphSmallArcs.md)
