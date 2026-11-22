# Exact integral image of circuit restriction

## Abstract

The dual parallel classes give the exact integral image along any matroid circuit.

**Theorem 1.1 (The class-size gcd times the contracted top-cycle lattice).**

Lean statement: `D5/S3/Combinatorics/Matroids/IntegralCircuitImage.exists_topCycle_aggregateRestrict_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/IntegralCircuitImage.exists_topCycle_aggregateRestrict_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a circuit in a matroid on a finite totally ordered carrier. Aggregate the signed restrictions obtained by removing one vertex at a time from the circuit face. At each basis of the contraction, each summand reads the coefficient on the union of the basis and the corresponding circuit facet. Its orientation is the product of the facet boundary sign and the shuffle sign. The image consists exactly of the gcd of the dual parallel-class sizes on K times the integral augmented top-cycle lattice of the contraction.

For two elements of one dual parallel class, the ridge missing those two elements gives a two-term boundary equation. Any other extension would have a dual base containing both elements. The oriented circuit boundary determines the relative signs in the equation. Thus the signed coordinates agree within the class and their aggregate is divisible by the class-size gcd. Dividing by that gcd preserves base support and the zero-boundary equations over the integers.

In the reverse direction, delete one parallel class and contract its complement in the circuit. Comparing bases through dual complements identifies this minor with the circuit contraction. The deletion has no coloops because contracting the rank-one flat in the dual leaves no loops. Multiply the target cycle by the shuffle sign of the class and its complement in the circuit, lift through the independent face, and join with the oriented simplex boundary on the class. The join contributes the same shuffle sign again. Each vertex in the class therefore contributes the original target cycle. An integer Bezout combination of these class-size multiples gives the gcd multiple. If the original matroid has a coloop, it survives the circuit contraction and the entire target top-cycle lattice is zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/IntegralCircuitImage.exists_topCycle_aggregateRestrict_iff`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitRestrictionImage](CircuitRestrictionImage.md)
- Dependency: [D5/S3/Combinatorics/Matroids/IntegralLinkRestriction](IntegralLinkRestriction.md)
