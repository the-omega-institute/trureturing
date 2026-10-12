# Direct prefix partitions and their two fan moments

## Abstract

A binary word traces positive unit steps in one oriented plane. Signed triangle sums give area and centered first moments, including paths of zero signed area. The reverse list of horizontal prefix counts at vertical letters is a padded decreasing partition. Its row and conjugate column squares determine the two centered moments of the same word at its direct area count.

**Definition 1.1 (One ordered path).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{G}\left(w\right) = \operatorname{Five}\left(\operatorname{q}\left(w\right).1, \operatorname{q}\left(w\right).2, 2\operatorname{A}\left(w\right), 12\operatorname{m}\left(w\right).1, 12\operatorname{m}\left(w\right).2\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

True is the horizontal unit step and false is the vertical unit step. Prefix sums are the vertices of the path. Each consecutive pair contributes its determinant divided by two and that signed area times the sum of its vertices divided by three. The centered vector is the raw moment minus half the area times the endpoint. The five coordinates are the endpoint, twice the signed area, and twelve times each centered moment. No division by the total area occurs.

**Definition 1.2 (The update using old coordinates).**

$$\forall x \in Five,\; \forall c \in Bool,\; \operatorname{U}\left(x, c\right) = \operatorname{if}\left(c, \operatorname{Five}\left(x.u+1, x.v, x.d-x.v, x.e-3x.d-x.u \cdot x.v+x.v, x.f-x.v^{2}\right), \operatorname{Five}\left(x.u, x.v+1, x.d+x.u, x.e+x.u^{2}, x.f-3x.d+x.u \cdot x.v-x.u\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All coordinates on the right are from the same old Five value. The true branch adds the horizontal unit step; the false branch adds the vertical unit step.

**Definition 1.3 (The common seam correction).**

$$\forall x \in Five,\; \forall y \in Five,\; \operatorname{star}\left(x, y\right) = \operatorname{Five}\left(x.u+y.u, x.v+y.v, x.d+y.d+(x.u \cdot y.v-x.v \cdot y.u), x.e+y.e+3(y.d \cdot x.u-x.d \cdot y.u)+(x.u \cdot y.v-x.v \cdot y.u)(x.u-y.u), x.f+y.f+3(y.d \cdot x.v-x.d \cdot y.v)+(x.u \cdot y.v-x.v \cdot y.u)(x.v-y.v)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.star` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seam determinant is x.u times y.v minus x.v times y.u. The area and both moment corrections use this same determinant and the signed areas of the same two paths.

**Theorem 1.4 (Appending a supplied letter).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall c \in Bool,\; \operatorname{G}\left(\operatorname{append}\left(w, [c]\right)\right) = \operatorname{U}\left(\operatorname{G}\left(w\right), c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PaddedWordPartition.G_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending a letter preserves the old vertices and adds their last triangle. The resulting arithmetic uses the old endpoint and old signed area. It is valid for the empty auxiliary word as well as every nonempty word.

**Theorem 1.5 (Concatenating two paths).**

$$\forall h \in \operatorname{List}\left(Bool\right),\; \forall k \in \operatorname{List}\left(Bool\right),\; \operatorname{G}\left(\operatorname{append}\left(h, k\right)\right) = \operatorname{star}\left(\operatorname{G}\left(h\right), \operatorname{G}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PaddedWordPartition.G_concat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five coordinates of a concatenation satisfy the signed fan concatenation formula. Both moment coordinates include the endpoint and signed-area seam terms of the same two paths.

**Theorem 1.6 (Reversing the complete word).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{G}\left(\operatorname{reverse}\left(w\right)\right) = \operatorname{Five}\left(\operatorname{G}\left(w\right).u, \operatorname{G}\left(w\right).v, -\operatorname{G}\left(w\right).d, \operatorname{G}\left(w\right).e, \operatorname{G}\left(w\right).f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PaddedWordPartition.G_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversal fixes both letter counts, negates signed area, and preserves both centered moment coordinates. This statement compares mathematical positive words in a common unit reference. It supplies no operation, acquisition, calibration, or reversal authority over a physical source.

**Definition 1.7 (Zero-padded reverse prefix rows).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{rows}\left([]\right) = [] \land (\operatorname{rows}\left(\operatorname{cons}\left(true, w\right)\right) = \operatorname{map}\left((x:Nat\mapsto x+1), \operatorname{rows}\left(w\right)\right) \land (\operatorname{rows}\left(\operatorname{cons}\left(false, w\right)\right) = \operatorname{append}\left(\operatorname{rows}\left(w\right), [0]\right)))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every false letter, record the number of preceding true letters, then reverse the recorded list. The list contains one entry for every false letter, including zero entries. Its sum is the scattered true-before-false count and each row is bounded by the total true count.

**Definition 1.8 (The actual Young diagram).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{diagram}\left(w\right) = \operatorname{ofRowLens}\left(\operatorname{rows}\left(w\right), \operatorname{rowsSorted}\left(w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.diagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decreasing padded list defines a Young diagram by its cells; rowsSorted(w) denotes its decreasing-order proof rows_sorted w. Zero entries stay in the padded list even though they contribute no cells. The row statistic is the sum of the row squares. The column statistic sums the squares of the rows of this very diagram's transpose, padded to the true count.

**Definition 1.9 (Squares of the padded rows).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{P}\left(w\right) = \sum_{i:\operatorname{Fin}\left(\operatorname{length}\left(\operatorname{rows}\left(w\right)\right)\right)} \operatorname{real}\left(\operatorname{rowLen}\left(\operatorname{diagram}\left(w\right), i\right)\right)^{2}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index ranges over every entry of the padded row list. The natural row length is cast to the reals before squaring.

**Definition 1.10 (Squares of the actual transpose rows).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{R}\left(w\right) = \sum_{j\in \operatorname{range}\left(\operatorname{count}\left(w, true\right)\right)} \operatorname{real}\left(\operatorname{rowLen}\left(\operatorname{transpose}\left(\operatorname{diagram}\left(w\right)\right), j\right)\right)^{2}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural column length is the row length of the same diagram's transpose. The sum ranges from zero to the true count minus one, including zero columns.

**Theorem 1.11 (Column squares from the same cells).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{R}\left(w\right) = \operatorname{oddRows}\left(\operatorname{rows}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PaddedWordPartition.same_diagram_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A column of height h has square equal to the sum of the first h odd positive integers. Summing over columns and interchanging the finite cell sums gives the odd-position weighted sum of the original rows. The equality uses membership in one diagram and its actual transpose.

**Theorem 1.12 (All words at direct area).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{G}\left(w\right) = \operatorname{Five}\left(\operatorname{real}\left(\operatorname{count}\left(w, true\right)\right), \operatorname{real}\left(\operatorname{count}\left(w, false\right)\right), 2\operatorname{real}\left(\operatorname{scatteredTrueFalseCount}\left(w\right)\right)-\operatorname{real}\left(\operatorname{count}\left(w, true\right)\right)\operatorname{real}\left(\operatorname{count}\left(w, false\right)\right), \operatorname{real}\left(\operatorname{count}\left(w, true\right)\right)^{2}\operatorname{real}\left(\operatorname{count}\left(w, false\right)\right)-6\operatorname{real}\left(\operatorname{count}\left(w, true\right)\right)\operatorname{real}\left(\operatorname{scatteredTrueFalseCount}\left(w\right)\right)+6\operatorname{P}\left(w\right), -\operatorname{real}\left(\operatorname{count}\left(w, true\right)\right)\operatorname{real}\left(\operatorname{count}\left(w, false\right)\right)^{2}+6\operatorname{real}\left(\operatorname{count}\left(w, false\right)\right)\operatorname{real}\left(\operatorname{scatteredTrueFalseCount}\left(w\right)\right)-6\operatorname{R}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PaddedWordPartition.all_word_direct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every binary word, with u true letters, v false letters, K scattered true-before-false pairs, row-square sum P and transposed column-square sum R, the exact coordinates are D = 2K - uv, E = u squared times v - 6uK + 6P, and F = minus u times v squared + 6vK - 6R. K is used directly, including values above half the rectangle area. Empty auxiliary words, pure-letter words and zero signed area need no additional hypothesis or division. Actual acquisition, common calibration and exact arithmetic remain independent premises when the formula is used for a physical source.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.G`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.G_append`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.G_concat`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.G_reverse`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.P`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.R`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.U`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.all_word_direct`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.diagram`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.rows`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.same_diagram_columns`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.star`
- Dependency: [D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge](../../Observer/GoldenChronology/BinaryParikhStepTwoBridge.md)
