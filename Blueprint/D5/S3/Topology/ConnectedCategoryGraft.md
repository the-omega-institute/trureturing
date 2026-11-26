# Ordinary category of a connected finite-space graft

## Abstract

Ordinary category of a connected finite-space graft

**Theorem 1.1 (The exact categorical cover number of the graft).**

Lean statement: `D5/S3/Topology/ConnectedCategoryGraft.hasCategoricalCover_graft_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/ConnectedCategoryGraft.hasCategoricalCover_graft_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Glue the height-one poset with two minima and m common maxima to a connected poset at a shared minimal point. The graft has a categorical lower cover with n pieces exactly when the original poset has such a cover and m is at most n. Each principal lower set of the height-one poset contracts to the shared point while fixing it. These contractions extend a cover of the original poset to the union. Any piece containing two new maxima would contract a retract whose identity is isolated among comparable maps, so the maxima require distinct pieces.

## References

- Truth anchor: `D5/S3/Topology/ConnectedCategoryGraft.hasCategoricalCover_graft_iff`
