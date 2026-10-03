# Seven-State Growth Diagrams

## Abstract

Origin-anchored rectangles containing at most three permutation points carry a growth diagram with seven partition labels.

**Definition 1.1 (Origin-anchored rectangles).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.rectangle`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.rectangle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

For a word p, a width w and a height h, the rectangle consists of the positions from zero through w minus one whose values in p are at most h. Values outside the word are taken to be zero.

**Definition 1.2 (The ambient Ferrers region).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.ferrersRegion`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.ferrersRegion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

For a nonnegative integer n, the Ferrers region is the union, over m from three through n, of the rectangles of positive cells with width n minus m plus three and height m.

**Definition 1.3 (Active heights).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.active`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.active` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

A height m is active for a word p of parameter n when three is at most m, m is at most n, and the rectangle of width n minus m plus three and height m contains exactly three positions.

**Definition 1.4 (The active region).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.activeRegion`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.activeRegion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The active region is the union of the positive-cell rectangles of width n minus m plus three and height m over all active heights m.

**Definition 1.5 (The seven partition labels).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.SevenLabel`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.SevenLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The seven labels represent the empty partition, the partition of one, the row and column partitions of two, and the row, hook and column partitions of three.

**Definition 1.6 (The size of a label).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.size`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.size` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The size of a label is the number of boxes in its partition: zero for the empty label, one for the single-box label, two for either two-box label and three for any three-box label.

**Definition 1.7 (Adjacent partition labels).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenEdge`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenEdge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Two labels are joined by an edge when they are equal or when the larger partition is obtained from the smaller by adding one box.

**Definition 1.8 (The inverse local rule).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenInverse`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenInverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The inverse local rule assigns a southwest label and a Boolean cell entry to a compatible triple of northeast, northwest and southeast labels. Its finite table is the partition growth rule restricted to the seven labels; triples absent from the table have no assigned value.

**Definition 1.9 (The forward local rule).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenForward`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenForward` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Given southwest, northwest and southeast labels and a Boolean cell entry, the forward local rule selects the first label, in the order empty, one, two-row, two-column, three-row, hook and three-column, whose inverse rule returns the prescribed southwest label and entry. It has no assigned value if there is no such label.

**Definition 1.10 (The growth diagram).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenDiagram`

*Formalization.* `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenDiagram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

The growth diagram has empty labels on the two coordinate axes. At each positive cell it applies the forward local rule to the three preceding labels and the entry indicating whether the permutation point occupies that cell. An undefined preceding label or local rule makes the new label undefined.

**Theorem 1.11 (Existence on rectangles of size at most three).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.seven_state_construction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.seven_state_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Let p be a permutation of one through n. Every origin-anchored rectangle with width and height at most n and at most three points has a defined growth-diagram label. The size of that label equals the number of points, and each defined label immediately to its west or south is joined to it by an edge.

**Theorem 1.12 (Increasing and decreasing rectangles).**

Lean statement: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.seven_order_interpretation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.seven_order_interpretation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuzhen Lv, Philip B. Zhang (2025). *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and Minus-Antipodal Shadings*. DOI: [10.48550/arXiv.2501.00357](https://doi.org/10.48550/arXiv.2501.00357). URL: <https://arxiv.org/abs/2501.00357v3>.

*Commentary.*

Let p be a permutation of one through n, and let an origin-anchored rectangle of width and height at most n contain at most three points and have label L. Its values are strictly increasing in position exactly when L is empty, one, two-row or three-row. They are strictly decreasing in position exactly when L is empty, one, two-column or three-column.

## References

- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.SevenLabel`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.active`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.activeRegion`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.ferrersRegion`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.rectangle`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenDiagram`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenEdge`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenForward`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.sevenInverse`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.seven_order_interpretation`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.seven_state_construction`
- Truth anchor: `D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.size`
- Dependency: [D5/S3/Combinatorics/MeshPattern/MeshPatternS21Defs](MeshPatternS21Defs.md)
