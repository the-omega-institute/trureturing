# Mixed weaving circles and spanning components

## Abstract

Mixed weaving circles and spanning components.

Let P have n at least two and m at least three, with cyclic time ZMod(m). For either parity p below two and any subset S of crossings, use the complementary local smoothing precisely at S and retain the actual external matching. The resulting quotient MixedCircle contains all components, including those meeting the closing seam. The reference graph has every uniform circle as a vertex and exactly the crossing incidences selected by S.

**Theorem 1.1 (Mixed weaving circles and spanning components).**

Lean statement: `D5/S3/Topology/WeavingMixedComponents.distinct_reference_components_force_distinct_mixed_circles`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingMixedComponents.distinct_reference_components_force_distinct_mixed_circles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sending a dart to its uniform circle and then to its spanning-graph component is constant on each actual mixed circle. At a selected crossing all four port classes belong to the same spanning component; at an unselected crossing the original local arc preserves its uniform circle. The external matching preserves that uniform circle as well. The map therefore descends to mixed circles with values in the full spanning-component quotient, including isolated vertices. For any two darts whose spanning components are distinct, their actual mixed-circle classes must be distinct as well. With every crossing selected the reference graph is connected: the actual wires connect consecutive generator positions, and the left seam advances cyclic time.

These finite matching statements are auxiliary to weaving coefficient asymptotics. They do not identify a state polynomial with the source trace-defined Jones invariant or establish the original twist-number limit.

## References

- Truth anchor: `D5/S3/Topology/WeavingMixedComponents.distinct_reference_components_force_distinct_mixed_circles`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit](../Combinatorics/PerfectMatchings/InvolutionOrbitSplit.md)
- Dependency: [D5/S3/Topology/WeavingDiagramPorts](WeavingDiagramPorts.md)
