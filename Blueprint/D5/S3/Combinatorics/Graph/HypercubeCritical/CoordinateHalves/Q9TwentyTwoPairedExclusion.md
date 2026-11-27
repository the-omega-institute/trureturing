# Exclusion of a 22-vertex half in the nine-cube

## Abstract

Q9TwentyTwoPairedExclusion

**Theorem 1.1 (An order-72 balanced cubic support has no 22-vertex half).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion.no_twenty_two_half`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion.no_twenty_two_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppressing the degree-two vertices yields a finite list of compressed halves. The singleton parity cases are incompatible with an opposite half of size fifty.

The remaining compression consists of two complete bipartite graphs on parts of sizes two and three, with the three terminals matched. Translate the root and permute the axes to obtain two possible seeds, indexed by whether the second axes of the root paths coincide.

For every compatible placement of the subdivisions, parity recovers the opposite half and forces a vertex of degree greater than three. This excludes the 22/50 cut in the order-72 component case of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion.no_twenty_two_half`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
