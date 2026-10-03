# Direct Sums and Primitive Words

## Abstract

Value cuts decompose doubled permutations into primitive direct-sum factors.

**Definition 1.1 (Shifted letters).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.shift`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.shift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Shifting a word by m adds m to every letter.

**Definition 1.2 (Direct sum of words).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.directSum`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.directSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The direct sum appends a word shifted by m to a first word.

**Definition 1.3 (Value cut).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.valueCut`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.valueCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A cut at k splits a word after 2k positions, with only values at most k before the cut and only larger values after it.

**Definition 1.4 (Primitive doubled word).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.primitive`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.primitive` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A word of size n is primitive when it has no value cut strictly between zero and n.

**Definition 1.5 (Indecomposable pattern).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.sumIndecomposable`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.sumIndecomposable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

At every nonempty proper split of a pattern, a letter on the right is at most a letter on the left.

**Theorem 1.6 (Direct sums preserve doubled support).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.directSum_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.directSum_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

The direct sum of doubled permutations of sizes m and n is a doubled permutation of size m plus n.

**Theorem 1.7 (An indecomposable occurrence lies on one side).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.indecomposable_sublist_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.indecomposable_sublist_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

An indecomposable pattern occurring across two value-separated blocks occurs wholly in one block.

**Theorem 1.8 (Increasing relabeling preserves indecomposability).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.indecomposable_map`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.indecomposable_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A strictly increasing relabeling of the positive letters of an indecomposable pattern remains indecomposable.

**Theorem 1.9 (Pattern occurrence in a direct sum).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.occurs_directSum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.occurs_directSum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

For a positive indecomposable pattern using every letter in its range, occurrence in a direct sum is equivalent to occurrence in one summand.

**Theorem 1.10 (Splitting a doubled permutation at a cut).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.valueCut_split_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.valueCut_split_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

A value cut of a doubled permutation yields two doubled permutations whose direct sum is the original word.

**Theorem 1.11 (Existence of a first primitive factor).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.first_primitive_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.first_primitive_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Every nonempty doubled permutation splits into an initial primitive factor and a remaining doubled permutation.

**Theorem 1.12 (Uniqueness of a primitive split).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.primitive_split_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.primitive_split_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Two primitive initial-factor decompositions of the same doubled word have equal cut sizes and equal factors.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.directSum`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.directSum_perm`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.first_primitive_factor`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.indecomposable_map`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.indecomposable_sublist_append`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.occurs_directSum_iff`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.primitive`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.primitive_split_unique`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.shift`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.sumIndecomposable`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.valueCut`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.valueCut_split_perm`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders](NonnestingBasicOrders.md)
