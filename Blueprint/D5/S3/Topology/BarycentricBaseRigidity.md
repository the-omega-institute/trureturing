# A maximal-face criterion for contiguity at every depth

## Abstract

A maximal-face criterion for contiguity at every depth

**Theorem 1.1 (Contiguity chains fix the original base vertices).**

Lean statement: `D5/S3/Topology/BarycentricBaseRigidity.contiguity_chain_fixes_original_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BarycentricBaseRigidity.contiguity_chain_fixes_original_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For each original base vertex a, suppose a is the only vertex that can be adjoined to every maximal base face incident to a. Then every contiguity chain starting at the inclusion fixes all original base vertices, at every common subdivision depth. The distance bound first restricts the image of a maximal face barycenter using the fixed vertices of that face. A second application restricts the next image of a to the faces that can be joined to that maximal face. Intersecting those restrictions leaves only the iterated singleton at a.

## References

- Truth anchor: `D5/S3/Topology/BarycentricBaseRigidity.contiguity_chain_fixes_original_vertices`
- Dependency: [D5/S3/Topology/BarycentricNeighborhoodIteration](BarycentricNeighborhoodIteration.md)
