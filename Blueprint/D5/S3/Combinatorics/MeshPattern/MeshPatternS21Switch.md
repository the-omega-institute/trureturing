# Transposition Inside the Active Region

## Abstract

Transposing the labels on an active boundary produces a permutation with the same active rectangles and the same points outside the active region.

**Theorem 1.1 (The active-region switch).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Switch.seven_active_switch`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Switch.seven_active_switch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Let p be a permutation of one through n. Its active outline has n downward steps and a cell list without repetitions covering exactly the active region. Peeling its labeled boundary returns the entries of p on those cells and an axis path with only empty labels. Transposing every boundary label yields a boundary whose peeling returns the entries of another permutation q of one through n and an axis path with only empty labels. The permutations agree outside the active region. For every m from three through n, their rectangles of width n minus m plus three and height m have equal point counts, agree on whether they contain a point of value m, and agree on whether their last column contains a point. They have the same active heights and active region.

## References

- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Switch.seven_active_switch`
- Dependency: [D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary](MeshPatternS21Boundary.md)
