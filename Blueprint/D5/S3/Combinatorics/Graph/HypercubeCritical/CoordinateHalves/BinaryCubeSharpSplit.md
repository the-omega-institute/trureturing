# Equality in the two-coordinate split bound

## Abstract

Opposite-section sums attain the six-cube minimum, with disjoint section supports within each pair.

**Definition 1.1 (Section at two fixed coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.twoSection`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.twoSection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix the first two bits of a binary word on Q(n + 2) to a and b. The remaining n bits index the section.

**Theorem 1.2 (The four section sizes add to the total weight).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.sites_card_two_sections`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.sites_card_two_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each supported vertex belongs to exactly one section, so the total weight is the sum of the four support sizes.

**Theorem 1.3 (Two nonzero opposite sums force a sharp split).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.sharp_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.sharp_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be a Q8 binary kernel word of weight at most twelve. Assume both opposite-section sums 00 + 11 and 10 + 01 are nonzero. Then f has weight exactly twelve. Each sum has support a full Q6 neighbor shell, and within each opposite pair the two section supports are disjoint.

Adding opposite section equations cancels the terms from the other pair, leaving a Q6 kernel word. Each nonzero sum has weight at least six. The budget of twelve is therefore exhausted by the two sums, and the binary support identity forces both overlaps to vanish. The minimum-support classification identifies both sums.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.sharp_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.sites_card_two_sections`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSharpSplit.twoSection`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport](BinaryCubeKernelSupport.md)
