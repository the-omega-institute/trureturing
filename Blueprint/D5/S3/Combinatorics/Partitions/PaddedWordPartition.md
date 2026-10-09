# Direct prefix partitions and their two fan moments

## Abstract

The reverse list of horizontal prefix counts at vertical letters is a padded decreasing partition. Its row and conjugate column squares determine the two centered moments of the same word at its direct area count.

**Definition 1.1 (Zero-padded reverse prefix rows).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{rows}\left([]\right) = [] \land (\operatorname{rows}\left(\operatorname{cons}\left(true, w\right)\right) = \operatorname{map}\left((x:Nat\mapsto x+1), \operatorname{rows}\left(w\right)\right) \land (\operatorname{rows}\left(\operatorname{cons}\left(false, w\right)\right) = \operatorname{append}\left(\operatorname{rows}\left(w\right), [0]\right)))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every false letter, record the number of preceding true letters, then reverse the recorded list. The list contains one entry for every false letter, including zero entries. Its sum is the scattered true-before-false count and each row is bounded by the total true count.

**Definition 1.2 (The actual Young diagram).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{diagram}\left(w\right) = \operatorname{ofRowLens}\left(\operatorname{rows}\left(w\right), \operatorname{rowsSorted}\left(w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.diagram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decreasing padded list defines a Young diagram by its cells; rowsSorted(w) denotes its decreasing-order proof rows_sorted w. Zero entries stay in the padded list even though they contribute no cells. The row statistic is the sum of the row squares. The column statistic sums the squares of the rows of this very diagram's transpose, padded to the true count.

**Definition 1.3 (Squares of the padded rows).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{P}\left(w\right) = \sum_{i:\operatorname{Fin}\left(\operatorname{length}\left(\operatorname{rows}\left(w\right)\right)\right)} \operatorname{real}\left(\operatorname{rowLen}\left(\operatorname{diagram}\left(w\right), i\right)\right)^{2}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index ranges over every entry of the padded row list. The natural row length is cast to the reals before squaring.

**Definition 1.4 (Squares of the actual transpose rows).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{R}\left(w\right) = \sum_{j\in \operatorname{range}\left(\operatorname{count}\left(w, true\right)\right)} \operatorname{real}\left(\operatorname{rowLen}\left(\operatorname{transpose}\left(\operatorname{diagram}\left(w\right)\right), j\right)\right)^{2}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/PaddedWordPartition.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural column length is the row length of the same diagram's transpose. The sum ranges from zero to the true count minus one, including zero columns.

**Theorem 1.5 (Column squares from the same cells).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{R}\left(w\right) = \operatorname{oddRows}\left(\operatorname{rows}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PaddedWordPartition.same_diagram_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A column of height h has square equal to the sum of the first h odd positive integers. Summing over columns and interchanging the finite cell sums gives the odd-position weighted sum of the original rows. The equality uses membership in one diagram and its actual transpose.

**Theorem 1.6 (All words at direct area).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{G}\left(w\right) = \operatorname{Five}\left(\operatorname{real}\left(\operatorname{count}\left(w, true\right)\right), \operatorname{real}\left(\operatorname{count}\left(w, false\right)\right), 2\operatorname{real}\left(\operatorname{scatteredTrueFalseCount}\left(w\right)\right)-\operatorname{real}\left(\operatorname{count}\left(w, true\right)\right)\operatorname{real}\left(\operatorname{count}\left(w, false\right)\right), \operatorname{real}\left(\operatorname{count}\left(w, true\right)\right)^{2}\operatorname{real}\left(\operatorname{count}\left(w, false\right)\right)-6\operatorname{real}\left(\operatorname{count}\left(w, true\right)\right)\operatorname{real}\left(\operatorname{scatteredTrueFalseCount}\left(w\right)\right)+6\operatorname{P}\left(w\right), -\operatorname{real}\left(\operatorname{count}\left(w, true\right)\right)\operatorname{real}\left(\operatorname{count}\left(w, false\right)\right)^{2}+6\operatorname{real}\left(\operatorname{count}\left(w, false\right)\right)\operatorname{real}\left(\operatorname{scatteredTrueFalseCount}\left(w\right)\right)-6\operatorname{R}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PaddedWordPartition.all_word_direct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every binary word, with u true letters, v false letters, K scattered true-before-false pairs, row-square sum P and transposed column-square sum R, the exact coordinates are D = 2K - uv, E = u squared times v - 6uK + 6P, and F = minus u times v squared + 6vK - 6R. K is used directly, including values above half the rectangle area. Empty auxiliary words, pure-letter words and zero signed area need no additional hypothesis or division. Actual acquisition, common calibration and exact arithmetic remain independent premises when the formula is used for a physical source.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.P`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.R`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.all_word_direct`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.diagram`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.rows`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PaddedWordPartition.same_diagram_columns`
- Dependency: [D5/S3/Combinatorics/Partitions/BinaryWordFan](BinaryWordFan.md)
- Dependency: [D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge](../../Observer/GoldenChronology/BinaryParikhStepTwoBridge.md)
