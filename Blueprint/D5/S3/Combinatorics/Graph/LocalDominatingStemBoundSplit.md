# The stem-conditioned split

## Abstract

The stem is selected, its leaves are free choices, and the residual set must dominate the vertices not adjacent to the stem.

**Theorem 1.1 (Family size).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.stem_family_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.stem_family_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of conditioned dominating sets is 2 to the number of leaves times the number of partially dominating residual sets.

**Theorem 1.2 (Total size of free leaf choices).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.powerset_card_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.powerset_card_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the sum of the sizes of all subsets of a finite set is its cardinality times the size of its powerset.

**Theorem 1.3 (Exact mean split).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.avdAt_stem_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.avdAt_stem_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local mean is one plus half the number of leaf neighbours plus the mean size of the partial residual family.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.avdAt_stem_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.powerset_card_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.stem_family_card`
- Dependency: [D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure](LocalDominatingStemBoundStructure.md)
