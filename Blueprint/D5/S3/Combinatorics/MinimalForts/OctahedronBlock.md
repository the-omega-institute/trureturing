# The octahedral block and its full finite counts

## Abstract

The octahedral block and its full finite counts.

**Definition 1.1 (The actual octahedral graph).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.octahedron`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.octahedron` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The graph is the complete equipartite graph on Fin 3 times Fin 2. Two vertices are adjacent exactly when their first coordinates differ. Thus the graph is finite, simple, undirected and loopless, with six vertices.

**Theorem 1.2 (Exact counts and no isolated vertices).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.octahedron_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.octahedron_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The conjunction states that the actual vertex type has cardinality six, the complete family of inclusion-minimal nonempty forts has cardinality eleven, the full rooted choice family has cardinality twelve, and every vertex has a neighbor. Kernel reduction checks every subset, including all possible proper fort subsets. This is a fixed-block ingredient, with no arbitrary-multiplicity or asymptotic conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.octahedron`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/OctahedronBlock.octahedron_block`
- Dependency: [D5/S3/Combinatorics/MinimalForts/UniversalRoot](UniversalRoot.md)
