# DendriteObstruction - ProperExpansion

## Abstract

Every proper subcontinuum has a proper continuum neighbourhood.

**Theorem 1.1 (Components of compact closed carriers).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ProperExpansion.compact_component`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/ProperExpansion.compact_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a compact subset F of a metric space and c in F, the ambient connectedComponentIn F c is compact. It is the image of the closed connected component of c in the compact subtype F.

**Theorem 1.2 (Every proper subcontinuum has a proper continuum neighbourhood).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ProperExpansion.proper_continuum_expansion`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/ProperExpansion.proper_continuum_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume X is compact metric and every pair of its points is joined by an actual continuous map of the closed real unit interval. For every nonempty compact connected proper subset C, there is a compact connected proper B with C contained in the interior of B.

If there were no such B, start with a continuous unit-interval-valued function zero near C and one on a nonempty open set. Remove the interior of its one-fiber, and take the component J containing C. Failure of the neighbourhood conclusion supplies a zero-neighbourhood point outside J. The compact subtype component equals the intersection of its clopen neighbourhoods, so a clopen separator splits the remaining closed carrier. Pasting half the old function and one minus half the old function yields the next continuous fold. The closed pieces overlap only on the one-fiber, where both formulas equal one half.

The functions have nested nonempty compact fibers at the fixed tent value two thirds. Choose a point in their intersection and a path from C to it. Composing this one path with the first function gives the fixed continuous interval map with tent lifts at every depth excluded by no_unbounded_tent_lifts. The conclusion uses no local connectedness, smoothness or branching bound.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ProperExpansion.compact_component`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ProperExpansion.proper_continuum_expansion`
- Dependency: [D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction](TentObstruction.md)
