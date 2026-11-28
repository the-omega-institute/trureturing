# Increasing prefixes and reverse outcomes

## Abstract

First-car deletion and the final arrival give exact recurrences for backgammon parking words.

**Theorem 1.1 (Count by deleting the increasing prefix).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.increasingPrefix_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.increasingPrefix_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

Delete the fixed prefix of k cars. Each shorter reverse-outcome word of rank r contributes the number of k successive lifts from rank r. A lift has one word of each rank from 1 through r + 1.

**Theorem 1.2 (Two cases for a reverse outcome).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.reverseOutcome_weight_succ_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.reverseOutcome_weight_succ_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

If car 1 starts in the final spot, deleting it leaves a reverse word and lowers the rank by one. Otherwise the final arrival bumps car 1 from spot 1 into the final vacancy. The preceding word is a one-car lift of a reverse word two cars shorter, and appending preference 1 preserves its rank.

**Theorem 1.3 (Count by longest distinct prefix).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.refinedCount_reverse_succ_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.refinedCount_reverse_succ_succ` (`✓ std3`). ∎

*Citation.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

The number at length m + 2 and rank j + 1 is the number at length m + 1 and rank j plus the sum at length m over ranks j through m. An empty street has one word of rank zero.

**Theorem 1.4 (The empty suffix).**

Lean statement: `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.increasingPrefix_count_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.increasingPrefix_count_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Clifton, Pamela E. Harris, and Maryam Khaqan (2026). *Parking Functions Inspired by Board Games*. DOI: [10.48550/arXiv.2611.29890](https://doi.org/10.48550/arXiv.2611.29890). URL: <https://arxiv.org/pdf/2611.29890v1>.

*Commentary.*

When the increasing prefix fills the street, its fiber is counted by the number of iterated lifts of the unique empty word.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.increasingPrefix_count`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.increasingPrefix_count_diagonal`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.refinedCount_reverse_succ_succ`
- Truth anchor: `D5/S3/Combinatorics/Parking/BackgammonReverseWeights.reverseOutcome_weight_succ_succ`
- Dependency: [D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix](BackgammonIncreasingPrefix.md)
