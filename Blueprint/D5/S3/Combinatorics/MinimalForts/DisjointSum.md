# All minimal forts of disjoint graph sums

## Abstract

All minimal forts of disjoint graph sums.

**Theorem 1.1 (Forthood on every disjoint subset).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/DisjointSum.fort_sum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/DisjointSum.fort_sum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For arbitrary finite decidable simple graphs G and H and arbitrary vertex subsets S and T, their disjoint sum is a fort exactly when at least one subset is nonempty and every unselected vertex of each summand has a selected-neighbor count different from one in that summand. Empty summands and empty intersections are retained.

**Theorem 1.2 (Complete minimality classification).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/DisjointSum.minimalFort_disjSum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/DisjointSum.minimalFort_disjSum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For arbitrary finite decidable simple graphs G and H, the disjoint subset S union T is an inclusion-minimal nonempty fort exactly when S is a minimal fort of G and T is empty, or S is empty and T is a minimal fort of H. Minimality ranges over all subsets.

**Theorem 1.3 (Exact additive full count).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/DisjointSum.minimalFort_sum_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/DisjointSum.minimalFort_sum_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For all finite decidable simple graphs G and H, the number of all actual minimal forts of their disjoint union equals the sum of their full minimal-fort counts. The proof constructs disjoint injective images and proves exhaustiveness, using the full minimality classification.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/DisjointSum.fort_sum_iff`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/DisjointSum.minimalFort_disjSum_iff`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/DisjointSum.minimalFort_sum_count`
- Dependency: [D5/S3/Combinatorics/MinimalForts/UniversalRoot](UniversalRoot.md)
