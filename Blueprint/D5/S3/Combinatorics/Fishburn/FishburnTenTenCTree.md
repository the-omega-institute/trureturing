# FishburnTenTenCTree

## Abstract

Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.

**Definition 1.1 (Four labels for the second classical class).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.CType`

*Formalization.* `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.CType` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For length n, the labels consist of an increasing type, a persistent type with a cut from zero through n minus two, a delayed type with a cut from zero through n minus three, and a terminal type with a cut from zero through n minus one. Persistent labels require n at least two, delayed labels require n at least three, and terminal labels require positive n.

**Definition 1.2 (Specifications of insertion positions and increasing prefixes).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.CSpec`

*Formalization.* `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.CSpec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

The increasing type is the increasing permutation with every position permitted for insertion of the next maximum. A persistent type with cut c is not increasing, has a strictly increasing prefix before c, and permits exactly positions c and n. A delayed type with cut c is not increasing and permits exactly positions c and n minus one. A terminal type with cut c permits only position c. Permitted insertion positions preserve avoidance of 231, 4132 and 2134.

**Theorem 1.3 (Unique classification of the second classical class).**

Lean statement: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.c_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.c_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Every permutation of length n avoiding 231, 4132 and 2134 satisfies the specification of exactly one increasing, persistent, delayed or terminal label, including its cut parameter when present.

## References

- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.CSpec`
- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.CType`
- Truth anchor: `D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.c_classification`
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalParents](FishburnBasicClassicalParents.md)
- Dependency: [D5/S3/Combinatorics/Fishburn/FishburnTenTenCTransitions](FishburnTenTenCTransitions.md)
