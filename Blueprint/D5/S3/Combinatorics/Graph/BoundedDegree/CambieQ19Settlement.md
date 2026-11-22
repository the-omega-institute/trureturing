# Connected induced supports and the two means

## Abstract

Every connected vertex support is an interval with permitted attachments or is confined to one attached block.

**Definition 1.1 (Actual tree subgraphs of a given order).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.SubtreesOfOrder`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.SubtreesOfOrder` (`✓ std3`).

*Citation.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

Choose a subgraph whose graph on its own vertices is a tree and whose vertex count is the specified order. The vertices and edges are both part of the subgraph.

**Definition 1.2 (Subtree counts by order).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.subtreeCount`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.subtreeCount` (`✓ std3`).

*Citation.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

The count at order k is the cardinality of the type of actual tree subgraphs with k vertices.

**Definition 1.3 (Total subtree count).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.totalSubtreeCount`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.totalSubtreeCount` (`✓ std3`).

*Citation.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

Sum the counts at all natural orders from one through the host cardinality.

**Definition 1.4 (Total subtree order).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.totalSubtreeOrder`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.totalSubtreeOrder` (`✓ std3`).

*Citation.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

Sum the product of the order and its subtree count from order one through the host cardinality.

**Definition 1.5 (Mean order of tree subgraphs).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.meanSubtreeOrder`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.meanSubtreeOrder` (`✓ std3`).

*Citation.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

Divide total subtree order by the total subtree count in the rationals.

**Definition 1.6 (Connected vertex sets).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.ConnectedSets`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.ConnectedSets` (`✓ std3`).

*Citation.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

A vertex set is counted once when its induced graph is connected.

**Definition 1.7 (Mean order of connected vertex sets).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.meanConnectedOrder`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.meanConnectedOrder` (`✓ std3`).

*Citation.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

For a finite vertex type, divide the sum of the connected-set cardinalities by their count in the rationals.

**Definition 1.8 (Question 1.9).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.claim` (`✓ std3`).

*Citation.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

Cambie, Jooken and Wagner ask whether the subtree mean is at least the connected-set mean for every connected graph. The quantification is over finite simple graphs. Singletons contribute to both means.

**Definition 1.9 (Cyclic intervals).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.CycleInterval`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.CycleInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The code is either the full cycle or a starting vertex and a positive length strictly smaller than the cycle size.

**Definition 1.10 (Vertices of a cyclic interval).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.cycleVertices`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.cycleVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full cycle uses every core vertex. A proper cyclic interval uses successive vertices from its start.

**Definition 1.11 (Order of a cyclic interval).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.cycleOrder`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.cycleOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order is the cycle size or the encoded positive length.

**Definition 1.12 (Order of a path interval).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.order`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.order` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order is the difference of the endpoints plus one.

**Definition 1.13 (Intervals in a path).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.PathInterval`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.PathInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An interval is given by its two path positions in weakly increasing order, both included.

**Theorem 1.14 (Preconnected nonempty supports).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.induced_connected_of_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.induced_connected_of_preconnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An induced subgraph on a nonempty vertex subset is connected whenever it is preconnected.

**Definition 1.15 (Permitted path prefixes).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.PathPrefix`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.PathPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prefix length is between zero and 500. A positive length requires selection of the path mark in the core.

**Definition 1.16 (Permitted triangle subsets).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.TriangleExtension`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.TriangleExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonempty triangle subset requires selection of core vertex 500 and triangle vertex 0.

**Definition 1.17 (The four support configurations).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.Configuration`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.Configuration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose a core interval with its permitted attachments, an interval of the first path alone, an interval of the second path alone, or a nonempty subset of the triangle alone.

**Definition 1.18 (Projection to core vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.coreSet`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.coreSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the preimage of a support under the core inclusion.

**Definition 1.19 (Projection to triangle vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.triangleSet`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.triangleSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the preimage of a support under the triangle inclusion.

**Definition 1.20 (Vertices of a decoded configuration).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.vertices`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.vertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the core interval together with its selected attachments, or the indicated support in a single attached block.

**Definition 1.21 (Order of the decoded configuration).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.vertexOrder`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.vertexOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a support meeting the core, add the core interval length, the two prefix lengths and the triangle cardinality. Otherwise use the order of the selected interval or triangle subset.

**Theorem 1.22 (Connectedness of the decoded support).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportConnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportConnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the four configurations induces a connected subgraph of the witness.

**Definition 1.23 (The connected-support equivalence).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decoding gives a bijection from the four interval-and-attachment cases to all actual connected induced supports of the witness.

**Theorem 1.24 (Vertex set of the inverse image).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv_symm_verts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv_symm_verts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse equivalence sends a configuration to the connected induced support whose vertex set is its decoded set.

**Theorem 1.25 (Pointwise preservation of support order).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cardinality of the connected support recovered from each configuration equals its decoded order.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.Configuration`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.ConnectedSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.CycleInterval`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.PathInterval`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.PathPrefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.SubtreesOfOrder`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.TriangleExtension`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.coreSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.cycleOrder`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.cycleVertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.induced_connected_of_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.meanConnectedOrder`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.meanSubtreeOrder`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.order`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.subtreeCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportConnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv_order`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.supportEquiv_symm_verts`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.totalSubtreeCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.totalSubtreeOrder`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.triangleSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.vertexOrder`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.vertices`
- Dependency: [D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph](CambieQ19Graph.md)
- Dependency: [D5/S3/Combinatorics/Graph/ZeroForcing/CycleConnectedForcing](../ZeroForcing/CycleConnectedForcing.md)
- Dependency: [D5/S3/Combinatorics/Graph/ZeroForcing/PathConnectedForcing](../ZeroForcing/PathConnectedForcing.md)
