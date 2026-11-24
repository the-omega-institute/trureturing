# Prescribed Returns in a Steiner Central Extension

## Abstract

Triple labels realize prescribed component returns in a central extension.

**Theorem 1.1 (Prescribing the returns throughout each component).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerSchreierExtension.realizeSchreierReturns`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerSchreierExtension.realizeSchreierReturns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Fix a finite centreless Steiner loop, two distinct nonidentity pivots, and a commutative additive group in which doubling is zero. The graph consists of the two pivot matchings. Assign an element of the group to each component other than the one through the identity.

The extension adds one group label for the triple traversed at each step. Within a component, the disjoint product orbits keep the two directions of a matching edge from occurring twice in one circuit. Outside the identity component, different matching edges use different triples. One chosen label per component therefore realizes all prescribed returns.

The first return to the fibre of any vertex shifts the fibre coordinate by the prescribed element. Conjugation by either matching step reverses the circuit and negates its return. Every group element equals its negative, so this gives the same return at all corners. The component through the identity has zero return. The extension is a Steiner loop, and its centre is exactly the fibre over the identity.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerSchreierExtension.realizeSchreierReturns`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit](../PerfectMatchings/InvolutionOrbitSplit.md)
