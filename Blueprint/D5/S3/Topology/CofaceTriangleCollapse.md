# Graph retraction from comparable cofaces

## Abstract

Graph retraction from comparable cofaces

**Theorem 1.1 (Comparable cofaces of bounded size give a contiguous graph retraction).**

Lean statement: `D5/S3/Topology/CofaceTriangleCollapse.exists_contiguous_graph_retraction`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CofaceTriangleCollapse.exists_contiguous_graph_retraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Label each vertex by a face with at most three vertices containing it. Suppose the labels of every source face form an inclusion chain. Each triangle has a vertex whose label equals the triangle and whose incident faces are all contained in it. Replace one such vertex per triangle by a different vertex of the triangle. The replacements define a retraction to a full graph subcomplex. The retraction followed by inclusion is contiguous to the identity, takes each vertex into its label, and fixes vertices whose labels have at most two elements.

## References

- Truth anchor: `D5/S3/Topology/CofaceTriangleCollapse.exists_contiguous_graph_retraction`
- Dependency: [D5/S3/Topology/BarycentricBaseRigidity](BarycentricBaseRigidity.md)
