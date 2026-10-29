# Mixed complete and octahedral blocks

## Abstract

Actual mixed-block graphs and their exhaustive minimal-fort counts.

**Definition 1.1 (The actual labelled vertices).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/MixedBlocks.Vertex`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/MixedBlocks.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For arbitrary nonnegative natural x,y,z,r, the base has x disjoint copies of the complete graph on six vertices, twice y disjoint triangles, z disjoint octahedral graphs, and one complete graph on r plus two vertices. The vertex type additionally contains one universal root. Zero multiplicities are permitted. The final complete block is always present.

**Definition 1.2 (The actual connected graph).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/MixedBlocks.graph`

*Formalization.* `D5/S3/Combinatorics/MinimalForts/MixedBlocks.graph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

The graph is the cone over the specified disjoint base. Every root-base edge is present; edges inside each labelled component are exactly those of its complete or octahedral graph; there are no other edges. All graphs are finite, simple, undirected, loopless and unweighted. The natural parameter r is not restricted to the six order residues.

**Theorem 1.3 (Exact order and all minimal forts).**

Lean statement: `D5/S3/Combinatorics/MinimalForts/MixedBlocks.mixed_graph_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MinimalForts/MixedBlocks.mixed_graph_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte (2024). *On the number of minimal forts of a graph*. DOI: [10.48550/arXiv.2404.05963](https://doi.org/10.48550/arXiv.2404.05963). URL: <https://arxiv.org/abs/2404.05963v1>.

*Commentary.*

For all nonnegative natural x,y,z,r, the actual graph has order six times the sum x+y+z, plus r plus three, is connected, and its entire minimal-fort count equals (r+2) times 6 to x times 9 to y times 12 to z, plus 15x plus 6y plus 11z plus the binomial coefficient choose(r+2,2). The octahedral numbers 11 and 12 come from the general whole-part and transversal classification for m two-vertex parts, specialized at m=3; its order is six. All actual inclusion-minimal nonempty forts are counted. Root-free counts add across components, while root-containing counts multiply. The proof includes arbitrary repeated blocks and zero-copy cases. The exponential root-containing term is used for asymptotic normalization; the root-free term grows at most linearly in the total block multiplicity.

## References

- Truth anchor: `D5/S3/Combinatorics/MinimalForts/MixedBlocks.Vertex`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/MixedBlocks.graph`
- Truth anchor: `D5/S3/Combinatorics/MinimalForts/MixedBlocks.mixed_graph_count`
- Dependency: [D5/S3/Combinatorics/MinimalForts/CompleteRooted](CompleteRooted.md)
- Dependency: [D5/S3/Combinatorics/MinimalForts/ConeCount](ConeCount.md)
- Dependency: [D5/S3/Combinatorics/MinimalForts/OctahedronBlock](OctahedronBlock.md)
- Dependency: [D5/S3/Combinatorics/MinimalForts/RootedProduct](RootedProduct.md)
