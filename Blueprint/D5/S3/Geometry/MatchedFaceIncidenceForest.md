# The incidence forest of a collapse sequence

## Abstract

The incidence forest of a collapse sequence

**Theorem 1.1 (A coface bound prevents cycles among deleted faces).**

Lean statement: `D5/S3/Geometry/MatchedFaceIncidenceForest.incidenceGraph_isAcyclic_of_sequence`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/MatchedFaceIncidenceForest.incidenceGraph_isAcyclic_of_sequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A fixed-dimensional collapse sequence orders the matched faces. Each lower face has at most one other original upper coface, which precedes its match. The maximum-rank vertex on a hypothetical incidence cycle would have two distinct predecessors.

## References

- Truth anchor: `D5/S3/Geometry/MatchedFaceIncidenceForest.incidenceGraph_isAcyclic_of_sequence`
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](FiniteRelativeSimplicialCollapse.md)
