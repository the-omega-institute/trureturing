# Three categorical pieces in dimensions four and five

## Abstract

Three categorical pieces in dimensions four and five

**Theorem 1.1 (The contractible three-piece bound).**

Lean statement: `D5/S3/Topology/StableCategory/ThreePieceCategoricalCover.three_pieces_of_contractible`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/ThreePieceCategoricalCover.three_pieces_of_contractible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A finite simplicial complex of dimension at most five with contractible realization admits three categorical subcomplexes at one ordinary barycentric subdivision depth.

The first two face ranks form a graph. In each round the graph parameter advances by four subdivisions while the ambient advances by three. The other region factors through a complex with four face ranks, including isolated vertices for exceptional components. Contractibility supplies a nullhomotopy of its final parameter map. Two categorical regions for that map pull back to collars, which together with the categorical graph collar cover at a common depth.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/ThreePieceCategoricalCover.three_pieces_of_contractible`
- Dependency: [D5/S3/Topology/StableCategory/FourPieceCategoricalCover](FourPieceCategoricalCover.md)
- Dependency: [D5/S3/Topology/StableCategory/LebesgueStarAssignment](LebesgueStarAssignment.md)
