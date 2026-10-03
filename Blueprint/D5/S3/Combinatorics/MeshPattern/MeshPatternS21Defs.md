# The Mesh Pattern Pair S21

## Abstract

The mesh patterns 123 and 321 with shading R = {0,1,2} squared together with {(3,3)} define two occurrence statistics on permutations.

**Definition 1.1 (The common shading).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.Shaded`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.Shaded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

A cell with column c and row r is shaded when both c and r are at most two, or when both equal three. Columns and rows are counted from zero.

**Definition 1.2 (The column of an additional position).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.column`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.column` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Relative to three selected positions i, j and k, the column of a position l is the number of selected positions strictly less than l.

**Definition 1.3 (The row of an additional value).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.row`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Relative to three selected values a, b and c, the row of a value x is the number of selected values strictly less than x.

**Definition 1.4 (Mesh occurrences).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.IsOccurrence`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.IsOccurrence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

A triple of strictly increasing positions within a word is an occurrence when its values are strictly increasing for the 123 pattern, or strictly decreasing for the 321 pattern, and every other position has its point outside the common shading. Positions are counted from zero.

**Definition 1.5 (The occurrence count).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.occ`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.occ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The occurrence count is the cardinality of the set of triples realizing the chosen mesh pattern. The Boolean parameter selects 123 when true and 321 when false.

**Definition 1.6 (Joint occurrence classes).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.joint`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.joint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

For nonnegative integers n, k and l, the joint class consists of the permutations of one through n having exactly k occurrences of the shaded 123 pattern and exactly l occurrences of the shaded 321 pattern.

**Definition 1.7 (Joint symmetry).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.claim`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

For all nonnegative integers n, k and l, the joint class with occurrence counts k and l has the same cardinality as the joint class with occurrence counts l and k.

## References

- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.IsOccurrence`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.Shaded`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.claim`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.column`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.joint`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.occ`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs.row`
