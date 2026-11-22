# Adjacent exchanges and prefix ranks

## Abstract

Adjacent exchanges and prefix ranks.

**Theorem 1.1 (One exchange).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges.exchange_prefix_ne_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges.exchange_prefix_ne_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Interchanging adjacent positions across rank d changes the unordered prefix exactly at rank d.

**Theorem 1.2 (A batch of exchanges).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges.batch_prefix_ne_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges.batch_prefix_ne_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Rossi (2026). *Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron*. DOI: [10.48550/arXiv.2611.25741](https://doi.org/10.48550/arXiv.2611.25741). URL: <https://arxiv.org/abs/2611.25741v1>.

*Commentary.*

Apply the exchanges in list order to the current permutation. For a list of distinct proper ranks, the final prefix differs from the original prefix exactly at the ranks in the list. At a given rank only the exchange across that rank can change its prefix.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges.batch_prefix_ne_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/PrefixExchanges.exchange_prefix_ne_iff`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension](../../Graph/PrefixHamming/ExactDimension.md)
