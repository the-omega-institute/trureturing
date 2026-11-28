# Five-dimensional fibres of the triangle-complement contact graph

## Abstract

Forbidden parity corrections constrain how the two components can occupy adjacent fibres.

In the seven-axis triangle-complement case of Hong, Wu and Xia's Problem 2, freeze the four clique axes. The three independent active axes and the two inactive axes remain free. The sixteen fibres are indexed by the four-cube. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Theorem 1.1 (Forbidden translations pack into the adjacent fibre).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.adjacent_fibre_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.adjacent_fibre_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A flip of the frozen axis moves to the adjacent fibre. Each forbidden free-axis correction restores the chosen parity and sends occupied points into positions excluded from the opposite component. Two different corrections differ by the involution that flips both free axes.

**Theorem 1.2 (At most eleven mixed fibres and at least five occupied pure fibres).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.five_axis_fibre_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.five_axis_fibre_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A mixed fibre holds at most six points on the chosen parity. An occupied pure fibre adjacent to a mixed fibre has at least two holes because a point of the opposite component forbids two distinct positions.

With twelve mixed fibres, each of the four remaining patterns has a mixed neighbour. The capacity is at most 12 times 6 plus 4 times 14, which is 128. With eleven mixed fibres, at most one of the other five patterns has all four neighbours among those five. Four occupied pure fibres can then contribute at most 16 plus 3 times 14, which again falls short of 129 after adding the mixed capacity.

**Theorem 1.3 (A mixed fibre contributes at most fifteen edges in the free directions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.mixed_five_axis_fibre_edge_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.mixed_five_axis_fibre_edge_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fibre with at most five occupied points on the chosen parity contributes at most fifteen edges by the degree bound. At occupancy six, the two components contribute one and five points. The five points are the free-coordinate neighbours of the singleton's antipode.

The antipode has five selected neighbours and is excluded by the degree bound. Each remaining edge from those five points comes from a selected double flip of the antipode. Signed flip anticommutation puts the two corresponding directions in opposite sign classes. Among five directions there are at most twelve ordered pairs across those classes, and the singleton contributes at most three more edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.adjacent_fibre_capacity`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.five_axis_fibre_counts`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9InactiveContactFibre.mixed_five_axis_fibre_edge_capacity`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator](Q9MinimumDistanceOperator.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCenter](Q9TightDistanceTwoCenter.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitSupportGap](../../HuangUnitSupportGap.md)
