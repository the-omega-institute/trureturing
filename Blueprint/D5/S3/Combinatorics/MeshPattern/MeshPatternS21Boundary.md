# Boundaries of Active Ferrers Regions

## Abstract

The active Ferrers region has a labeled boundary compatible with the seven-state local rule, and every active rectangle contributes a specified boundary corner.

**Definition 1.1 (A labeled boundary).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.sevenBoundary`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.sevenBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

A boundary direction word uses false for a downward step and true for a rightward step. Starting from the given column and the total number of downward steps, the labeled boundary pairs each direction with the label at the endpoint of its step.

**Definition 1.2 (The outline of a region).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.sevenOutline`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.sevenOutline` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Starting at a specified column and row, the outline moves right when the next cell lies in the region and the column bound has not been reached; otherwise it moves down. It ends when the row is zero.

**Definition 1.3 (Partition transposition).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.transpose`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.transpose` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Transposition exchanges the two-box row and column labels and the three-box row and column labels. It fixes the empty, one-box and hook labels.

**Theorem 1.4 (The active outline).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.seven_active_outline`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.seven_active_outline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

For a permutation of one through n, the active outline starts at column zero and row n and has n downward steps. Its cell list has no repetitions and consists exactly of the active region. The boundary labels form a seven-state path ending with the empty label, and at every listed cell the inverse local rule recovers the southwest label and the permutation entry.

**Theorem 1.5 (Corners at active heights).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.seven_corner_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.seven_corner_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

For a permutation of one through n and an active height m, the active outline factors into a prefix, a rightward step and a suffix such that the prefix has n minus m plus two rightward steps and the suffix has m downward steps. Thus the selected step ends at column n minus m plus three and row m.

## References

- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.sevenBoundary`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.sevenOutline`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.seven_active_outline`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.seven_corner_boundary`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.transpose`
- Dependency: [D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling](MeshPatternS21Peeling.md)
