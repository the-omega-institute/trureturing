# Hyperfiniteness of Golden Rotation and Asynchronous Merging

## Abstract

Hyperfiniteness of Golden Rotation and Asynchronous Merging.

**Theorem 1.1 (Finite Borel approximations from shrinking markers).**

Lean statement: `D5/S1/Digit/Infinite/MarkerHyperfiniteness.marker_hyperfiniteness`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/MarkerHyperfiniteness.marker_hyperfiniteness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the circle of circumference one, take the open marker arc of length one divided by the sum of n and two. Choose the least positive odd index j for which alpha to the power given by j plus two is smaller than this length. Write h for that power, Q for the corresponding Fibonacci return time, M for the floor of one divided by h, B for Q times M, and L for B plus one. The arcs are open, decrease, and have empty intersection. Every integer interval from a through a plus B contains a visit to the arc, so visits are unbounded in both directions and adjacent marked sources are at most L steps apart. Delete exactly the rotation edges whose sources lie in the arc and allow finite undirected paths, including empty paths, through the retained edges. The resulting relation is a Borel equivalence with classes of at most L points. These relations increase with n and their union is the rotation-orbit relation. Their pullbacks along the phase map of legal streams are increasing Borel equivalences with classes of at most twice L points, and their union is asynchronous eventual merging. Both relations are therefore hyperfinite: each is the union of an increasing family, indexed by all natural numbers, of Borel equivalences with finite classes. Here Borel measurability of a relation means that its graph is Borel for the product topology. The classical theorem of Slaman and Steel and of Weiss identifies Borel integer actions as the source of hyperfinite orbit equivalence relations; the explicit marker construction gives the stated class bounds.

## References

- Truth anchor: `D5/S1/Digit/Infinite/MarkerHyperfiniteness.marker_hyperfiniteness`
- Dependency: [D5/S1/Digit/Infinite/PhaseOrbitRelations](PhaseOrbitRelations.md)
- Dependency: [D5/S1/Digit/Infinite/WindowSuccessorGraph](WindowSuccessorGraph.md)
