# FishburnTenSevenAuxiliary

## Abstract

Fishburn permutations avoiding 213 decompose at their first entry and their maximum.

**Theorem 1.1 (Decomposition at the first entry).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary.H_head_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary.H_head_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

A list is a Fishburn permutation of length size plus one avoiding 213 if and only if there is a Fishburn permutation q of length size avoiding 213 such that the list is either size plus one followed by q, or one followed by q with every entry increased by one.

**Definition 1.2 (Decomposition at the maximum).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary.H_maximum_equiv`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary.H_maximum_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For every positive size, this bijection identifies Fishburn permutations of length size avoiding 213 with pairs consisting of a cut from zero through size minus one and a Fishburn permutation of length size minus cut minus one avoiding 213.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary.H_head_decomposition`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary.H_maximum_equiv`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicAscents](../Fishburn/FishburnBasicAscents.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicThreePatterns](../Fishburn/FishburnBasicThreePatterns.md)
