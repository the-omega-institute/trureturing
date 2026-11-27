# Categorical covers for the small acyclic census

## Abstract

Categorical covers for the small acyclic census

**Theorem 1.1 (Each listed finite order has an ordinary categorical two-cover).**

Lean statement: `D5/S3/Topology/SmallAcyclicCategoricalCovers.categorical_cover_of_census_table`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/SmallAcyclicCategoricalCovers.categorical_cover_of_census_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Each of the 105 order tables carries two lower sets and explicit contractions by comparable monotone maps. Lean checks the order, the cover and every comparison by kernel reduction. The list comes from the published Hasse census and the one-point-extension argument.

## References

- Truth anchor: `D5/S3/Topology/SmallAcyclicCategoricalCovers.categorical_cover_of_census_table`
- Dependency: [D5/S3/Topology/FiniteCategoricalCoverCertificate](FiniteCategoricalCoverCertificate.md)
