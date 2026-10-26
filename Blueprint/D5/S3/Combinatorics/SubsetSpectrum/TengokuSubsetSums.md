# Multiset subset sums

## Abstract

The multiset powerset records every occurrence of a subset sum.

**Definition 1.1 (The full occurrence spectrum).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums.subsetSums`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums.subsetSums` (`✓ std3`).

*Citation.* James Huang, Samuël Borza (2026). *Tengoku subset-sum and powerset-map leaves*. URL: <https://github.com/competemath/tengoku/tree/e784113248524aeef7681b0687c722b426c1b115>.

*Commentary.*

For a multiset in an additive commutative monoid, sum each member of its multiset powerset, retaining all resulting occurrences.

**Theorem 1.2 (Mapping and the powerset).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums.powerset_map_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums.powerset_map_eq` (`✓ std3`). ∎

*Citation.* James Huang, Samuël Borza (2026). *Tengoku subset-sum and powerset-map leaves*. URL: <https://github.com/competemath/tengoku/tree/e784113248524aeef7681b0687c722b426c1b115>.

*Commentary.*

Mapping a function over every member of a multiset powerset equals the powerset of the mapped multiset, even for a noninjective function.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums.powerset_map_eq`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums.subsetSums`
