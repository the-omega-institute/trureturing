# Categorical cover certificates for finite posets

## Abstract

Categorical cover certificates for finite posets

**Theorem 1.1 (Order tables and zigzags certify an ordinary categorical cover).**

Lean statement: `D5/S3/Topology/FiniteCategoricalCoverCertificate.hasCategoricalCover_of_tables`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteCategoricalCoverCertificate.hasCategoricalCover_of_tables` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A finite order table and two lower sets carry explicit sequences of vertex maps. Each sequence starts at the inclusion, ends at a constant, and consists of monotone maps with pointwise comparable neighbors. The checked data give a categorical cover in the ordinary finite-space sense.

**Theorem 1.2 (A checked zigzag contracts the inclusion of an induced subposet).**

Lean statement: `D5/S3/Topology/FiniteCategoricalCoverCertificate.categorical_of_table`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteCategoricalCoverCertificate.categorical_of_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

The Boolean domain can be any vertex subset. The checked monotone maps give a contraction in the ambient finite poset. Two such subsets covering the vertices supply the input for the subdivision transfer.

## References

- Truth anchor: `D5/S3/Topology/FiniteCategoricalCoverCertificate.categorical_of_table`
- Truth anchor: `D5/S3/Topology/FiniteCategoricalCoverCertificate.hasCategoricalCover_of_tables`
- Dependency: [D5/S3/Topology/ConnectedCategoryGraft](ConnectedCategoryGraft.md)
