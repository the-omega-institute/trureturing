# FishburnTenTenBTree

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Definition 1.1 (Four types of insertion-position labels).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.BType`

*Formalization.* `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.BType` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For length n, the labels consist of an increasing type, an adjacent type with a parameter from zero through n minus two, a persistent type with a parameter from zero through n minus three, and a terminal type with a parameter from zero through n minus two. The adjacent and terminal parameter sets are empty for n less than two, and the persistent parameter set is empty for n less than three.

**Definition 1.2 (Specifications of the four classical types).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.BSpec`

*Formalization.* `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.BSpec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

The increasing type is the increasing permutation with every position permitted for insertion of the next maximum. An adjacent type with parameter c permits exactly positions c plus one and c plus two; if c plus two equals n, the prefix before c plus one and the suffix beginning there are increasing and the two entries across the cut form a descent. A persistent type with parameter c has these same increasing pieces and descent at c plus one, and permits exactly positions c plus one and n. A terminal type with parameter c permits only position c plus one. Permitted insertion positions preserve avoidance of 321, 2143 and 3124.

**Theorem 1.3 (Classification of the first classical class).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.b_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.b_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Every permutation of length n avoiding 321, 2143 and 3124 satisfies the specification of at least one of the increasing, adjacent, persistent or terminal types. The specification records its permitted positions for insertion of the next maximum and the required increasing pieces.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.BSpec`
- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.BType`
- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.b_classification`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalParents](FishburnBasicClassicalParents.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions](FishburnTenTenBTransitions.md)
