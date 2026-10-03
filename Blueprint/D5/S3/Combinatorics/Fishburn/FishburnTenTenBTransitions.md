# FishburnTenTenBTransitions

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Theorem 1.1 (Transitions after internal maximum insertion).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions.b_internal_transition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions.b_internal_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a permutation of length n avoiding 321, 2143 and 3124. Suppose inserting n plus one at a position s strictly less than n preserves these conditions. Inserting n plus two into the resulting child at a position g from zero through n plus one preserves the same conditions exactly when g equals s plus one, or when g equals s plus two and inserting n plus one at position s plus one in p also preserves the same conditions.

**Theorem 1.2 (Transitions after appending the maximum).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions.b_append_transition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions.b_append_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Let p be a permutation of length n avoiding 321, 2143 and 3124, and suppose appending n plus one preserves these conditions. Inserting n plus two into this child at a position g from zero through n plus one preserves the conditions exactly when g equals n plus one, or when g is at most n and both the prefix of p before g and the suffix of p beginning at g are strictly increasing.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions.b_append_transition`
- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions.b_internal_transition`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasic2143](FishburnBasic2143.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalPatterns](FishburnBasicClassicalPatterns.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicPatterns](FishburnBasicPatterns.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnClassicalDefs](FishburnClassicalDefs.md)
