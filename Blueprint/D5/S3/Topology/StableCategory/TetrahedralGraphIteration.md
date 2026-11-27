# Refining a two-colour graph factorization

## Abstract

Refining a two-colour graph factorization

**Theorem 1.1 (One round of ordinary subdivision).**

Lean statement: `D5/S3/Topology/StableCategory/TetrahedralGraphIteration.refine_bicolour_graphs`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/TetrahedralGraphIteration.refine_bicolour_graphs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Each colour begins with a contiguity factorization through a properly two-coloured parameter graph. After three ordinary ambient subdivisions the two new induced regions factor through four subdivisions of the original parameter graphs. On the main regions the tetrahedral heights give the extra refinement. Each remaining component contracts along one opposite-colour edge and moves by an ambient edge path to the chosen parameter vertex.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/TetrahedralGraphIteration.refine_bicolour_graphs`
- Dependency: [D5/S3/Topology/GeometricGraphTermination](../GeometricGraphTermination.md)
