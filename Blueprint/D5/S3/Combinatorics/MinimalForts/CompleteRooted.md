# Root-containing choices of a complete block

## Abstract

Root-containing choices of a complete block.

**Theorem 1.1 (All rooted choices are singletons).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/CompleteRooted.complete_rooted_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/CompleteRooted.complete_rooted_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every finite decidable vertex type with at least two vertices, and every subset S, adjoining the universal root to S in the cone over the complete graph gives a minimal nonempty fort exactly when S has cardinality one. The empty subset and all larger subsets are included in the equivalence.

**Theorem 1.2 (The full rooted count).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/CompleteRooted.complete_rooted_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/CompleteRooted.complete_rooted_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For every finite decidable nontrivial vertex type V, the full rooted choice family of the complete graph has cardinality equal to the cardinality of V. The singleton map is an injective and exhaustive correspondence, rather than a choice of only some minimal forts.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/CompleteRooted.complete_rooted_count`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/CompleteRooted.complete_rooted_iff`
- Dependency: [D5/S3/Combinatorics/MinimalForts/CompleteBlock](CompleteBlock.md)
- Dependency: [D5/S3/Combinatorics/MinimalForts/UniversalRoot](UniversalRoot.md)
