# The cycle, paths and triangle of the counterexample

## Abstract

The graph has a 5,000-cycle, two 500-vertex paths attached at cycle vertices 0 and 1,000, and a triangle attached at vertex 500. Each attachment is a single bridge to vertex 0 in its block.

**Definition 1.1 (Joining two graphs at designated vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The disjoint sum gains the edge from the designated left vertex to the designated right vertex.

**Theorem 1.2 (Left adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_inl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_inl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two left vertices are adjacent exactly when they are adjacent in the left graph.

**Theorem 1.3 (Right adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_inr`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_inr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two right vertices are adjacent exactly when they are adjacent in the right graph.

**Theorem 1.4 (Cross adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_cross`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A left vertex and a right vertex are adjacent exactly when both are the designated endpoints.

**Definition 1.5 (The 6,003 labeled vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex set is the disjoint sum of the 5,000 core positions, two sets of 500 path positions and three triangle positions.

**Definition 1.6 (Core positions).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.core`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion sends each of the 5,000 core positions to its vertex in the disjoint sum.

**Definition 1.7 (First path positions).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.firstPath`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.firstPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion sends each of the 500 first-path positions to its vertex in the disjoint sum.

**Definition 1.8 (Second path positions).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.secondPath`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.secondPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion sends each of the 500 second-path positions to its vertex in the disjoint sum.

**Definition 1.9 (Triangle positions).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.triangle`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.triangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion sends each of the three triangle positions to its vertex in the disjoint sum.

**Definition 1.10 (The witness graph).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.G500`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.G500` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Join the 5,000-cycle first to the path at 0, then to the path at 1,000, and then to the triangle at 500, in each case using position 0 in the attached block.

**Theorem 1.11 (Connectedness of the witness).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.G500_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.G500_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Paths inside the four blocks and the three joining edges connect all vertices of the witness graph.

**Definition 1.12 (Restriction to the left vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.leftSet`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.leftSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the preimage of the support under the left inclusion.

**Definition 1.13 (Restriction to the right vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.rightSet`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.rightSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the preimage of the support under the right inclusion.

**Definition 1.14 (Splitting an induced vertex type).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitIso`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The disjoint sum of the two support restrictions is isomorphic to the induced graph via the canonical sum equivalence and pullback of adjacency.

**Theorem 1.15 (Left induced graph).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_inl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_inl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pulling back the induced join to the left restriction gives the corresponding induced left graph.

**Theorem 1.16 (Right induced graph).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_inr`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_inr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pulling back the induced join to the right restriction gives the corresponding induced right graph.

**Theorem 1.17 (Cross adjacency in the induced graph).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_cross`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cross edge is present between two selected endpoints exactly when they are the designated joining vertices.

**Theorem 1.18 (Induced connectivity across one bridge).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_induce_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_induce_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An induced support is connected exactly when it is nonempty, its two side restrictions are preconnected, and the designated endpoints are both selected whenever both sides are nonempty.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.G500`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.G500_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.core`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.firstPath`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_cross`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_induce_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_inl`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.joinAt_inr`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.leftSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.rightSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.secondPath`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_cross`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_inl`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitGraph_inr`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.splitIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.triangle`
