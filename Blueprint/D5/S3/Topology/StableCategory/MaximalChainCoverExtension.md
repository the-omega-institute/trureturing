# Extending categorical covers across maximal elements

## Abstract

Extending categorical covers across maximal elements

**Theorem 1.1 (A covering condition on maximal lower chains extends two prescribed categorical pieces).**

Lean statement: `D5/S3/Topology/StableCategory/MaximalChainCoverExtension.exists_relative_two_cover_of_maximal_lower_chains`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/MaximalChainCoverExtension.exists_relative_two_cover_of_maximal_lower_chains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Delete a selected set of maximal elements of a finite poset. Suppose two categorical lower sets of chains cover the chains that avoid those elements. For each deleted maximum choose a strict predecessor on each side. Every maximal lower chain at that maximum must belong to one of the prescribed pieces and contain the predecessor chosen for that side. The proof extends each piece with the chains on which adjoining the chosen predecessor and then removing the maximum retracts the chain into that piece. The two comparisons and the retraction fix the old chains, so the extended cover has the prescribed old intersections.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/MaximalChainCoverExtension.exists_relative_two_cover_of_maximal_lower_chains`
- Dependency: [D5/S3/Topology/ConnectedCategoryGraft](../ConnectedCategoryGraft.md)
