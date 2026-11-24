# Alternating Components over the Central Quotient of a Steiner Loop

## Abstract

A central return translation determines the size and number of lifted components.

**Theorem 1.1 (The component size and multiplicity over the central quotient).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSwitchQuotient.point_deleted_component_lifts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSwitchQuotient.point_deleted_component_lifts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Suppose the deleted point and the retained pivot of a finite complete Steiner triple system have distinct nonidentity classes in the quotient by the centre. The theorem constructs the quotient map by central orbits and descends the two matching translations. Their union on the quotient is a graph with two distinct projected partners at each vertex.

Over a quotient component C, the least period of the product of the two steps is half its size. After one such period upstairs, the lifted point returns to its fibre. This return is multiplication by a central element. Put d equal to one for the identity element and two otherwise. The lifted components have size d times the size of C, and their number times d equals the size of the centre.

The two parity classes of an alternating walk are disjoint forward orbits of the two-step map. Equivariance reduces repeated returns to powers of a single central element. Each base fibre has the size of the centre. Lifting paths and translating by the centre show that all components over C have the same size, so their total vertex count gives the multiplicity.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSwitchQuotient.point_deleted_component_lifts`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSwitchCentre](SteinerSwitchCentre.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AlternatingComponentParity](../PerfectMatchings/AlternatingComponentParity.md)
