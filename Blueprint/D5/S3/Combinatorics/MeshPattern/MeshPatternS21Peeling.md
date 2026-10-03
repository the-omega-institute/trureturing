# Peeling Seven-State Boundaries

## Abstract

Peeling a seven-state boundary reconstructs its cells, conserves row and column weights, and determines the original labels uniquely.

**Definition 1.1 (Seven-state boundary paths).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenPath`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenPath` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

A labeled direction word is a seven-state path from a starting label when every rightward step follows an edge from the current label to the next label and every downward step follows an edge from the next label to the current label. The empty word is a path from every label.

**Definition 1.2 (Sliding one column).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenSlide`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenSlide` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

A column slide moves a rightward step across the following downward steps. At each crossed cell the inverse local rule supplies its entry and southwest label. The slide returns the resulting labeled boundary and the entries of the crossed cells, or is undefined if a local rule is undefined.

**Definition 1.3 (Boundary peeling).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenPeel`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenPeel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Boundary peeling recursively processes the remaining direction word, retaining downward steps and sliding each rightward step across the resulting boundary. Its value is a labeled axis path together with a list of cells and Boolean entries, unless a required slide is undefined.

**Definition 1.4 (Row weights).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenRowWeight`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenRowWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The weight of a row is the sum of the decreases in partition size along the downward steps at that row. A step is at one plus the number of downward steps remaining after it.

**Definition 1.5 (Column weights).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenColumnWeight`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenColumnWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The weight of a column is the sum of the increases in partition size along rightward steps entering that column. The initial column is specified, and each rightward step increments it by one.

**Definition 1.6 (The area beneath a direction word).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenArea`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenArea` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The area is the sum, over all rightward steps, of the number of downward steps that follow them.

**Definition 1.7 (The ordered cell list).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenCells`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenCells` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The cell list assigns to each rightward step the cells in its new column from its current height down to row one. Columns are processed from the rightmost to the leftmost, and downward steps contribute no cells.

**Theorem 1.8 (Existence and shape of peeling).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_boundary_peeling`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_boundary_peeling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Every seven-state path can be peeled. The resulting axis path is again a seven-state path, has all downward steps before all rightward steps, has the same direction multiset and terminal label as the original path, and its returned cells have exactly the ordered cell coordinates of the original direction word. If both the initial and terminal labels are empty, every label on the axis path is empty.

**Theorem 1.9 (Conservation and sparsity).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_peeling_conservation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_peeling_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

For any seven-state path and its peeling, the original weight in each row equals the axis-path weight in that row plus the number of true entries returned in that row. The corresponding equality holds for every column. In each row and each column, at most one returned entry is true.

**Theorem 1.10 (Uniqueness from the peeled data).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_peeling_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_peeling_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Two seven-state paths with the same initial label, initial column and direction word are equal whenever their peelings return the same labeled axis path and the same cell entries.

## References

- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenArea`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenCells`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenColumnWeight`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenPath`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenPeel`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenRowWeight`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.sevenSlide`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_boundary_peeling`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_peeling_conservation`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.seven_peeling_unique`
- Dependency: [D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven](MeshPatternS21Seven.md)
