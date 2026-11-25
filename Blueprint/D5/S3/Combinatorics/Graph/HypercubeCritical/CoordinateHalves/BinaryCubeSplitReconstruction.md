# Reconstructing the two shells of a sharp split

## Abstract

The two opposite pairs determine adjacent six-cube centers and recover the full eight-cube word.

**Definition 1.1 (Open neighborhood of a cube vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.neighborhood`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.neighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The neighborhood of p consists of all vertices reached from p by a single coordinate flip.

**Definition 1.2 (Point indicator).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.delta`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word δₚ is one at p and zero elsewhere.

**Theorem 1.3 (Adjacency of a point indicator gives its neighbor shell).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.adjacency_delta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.adjacency_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjacency sum of δₚ at x is one precisely when x is a neighbor of p. A neighbor reaches p by a unique coordinate flip, so that flip is the sole nonzero summand.

**Theorem 1.4 (Each opposite pair splits its shell into one and five sites).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.sharp_split_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.sharp_split_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a Q8 binary kernel word has weight at most twelve and both opposite-section sums are nonzero. Its weight is twelve and the sums are the shells of two adjacent centers p and q in Q6. The equal-bit sections partition the shell at p into the singleton q and its five-site complement in that shell. The unequal-bit sections partition the shell at q into the singleton p and its five-site complement. Either orientation of each partition is allowed.

The adjacency of either section is the opposite sum from the other pair. Its image thus has six sites. The partial-shell count s(6 − s) plus the residue of s modulo two forces s to be one or five. The image of a singleton is its entire shell, and the shell in Q6 identifies its center, so each singleton is the other shell's center.

**Theorem 1.5 (A sharp split lifts to two shells with centers at distance two).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.sharp_split_two_shells`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.sharp_split_two_shells` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, the weight is twelve and the full word is the adjacency of the sum of two point indicators on Q8. Write s,s for the leading bits of the section containing only q and t,¬t for those of the section containing only p. The lifted centers have tails p and q and leading bits ¬s,¬s and ¬t,t, respectively.

The lifted centers differ in one leading bit and one tail bit. Taking the four sections of the adjacency of their sum gives the singleton and shell-complement words from the reconstruction, so the full word agrees in every section.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.adjacency_delta`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.delta`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.neighborhood`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.sharp_split_reconstruction`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction.sharp_split_two_shells`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubePartialShell](BinaryCubePartialShell.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit](BinaryCubeSharpSplit.md)
