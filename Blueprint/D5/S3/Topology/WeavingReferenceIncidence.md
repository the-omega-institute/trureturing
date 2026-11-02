# Crossing labels and graph edges

## Abstract

Crossing labels and graph edges.

**Definition 1.1 (Crossing labels and graph edges).**

Lean statement: `D5/S3/Topology/WeavingReferenceIncidence.crossingEdgeEquiv`

*Formalization.* `D5/S3/Topology/WeavingReferenceIncidence.crossingEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let n be at least two, m at least three and p either parity. Uniform-circle codes distinguish all interval columns and both outer hubs. A cup-cap crossing joins consecutive cyclic times in a single column. A vertical crossing joins two distinct column codes, with the boundary hub time fixed to zero. The unordered endpoint pair determines the crossing: reversing a row edge would force two to vanish modulo m, which is impossible for m at least three. Vertical edge times are recovered from an interval endpoint. Consequently the crossing labels biject with the simple reference graph edges, with exactly nm edges.

## References

- Truth anchor: `D5/S3/Topology/WeavingReferenceIncidence.crossingEdgeEquiv`
- Dependency: [D5/S3/Topology/WeavingMixedComponents](WeavingMixedComponents.md)
