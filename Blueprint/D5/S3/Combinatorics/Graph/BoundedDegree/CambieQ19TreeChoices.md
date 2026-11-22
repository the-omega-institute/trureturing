# Tree subgraphs on each connected support

## Abstract

Once the support is fixed, the freedom is to delete one actual edge independently from each fully included cycle.

**Definition 1.1 (A choice for one cycle restriction).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.CycleChoice`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.CycleChoice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A choice is an optional actual edge of the graph, present precisely when the support contains every vertex.

**Definition 1.2 (Independent core and triangle choices).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.DeletionChoices`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.DeletionChoices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the product of the choices for the restrictions of the core cycle and the triangle.

**Definition 1.3 (The actual tree fiber).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.TreeFiber`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.TreeFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A member is an actual tree subgraph of the host whose vertex set equals the specified support.

**Definition 1.4 (The tree-fiber equivalence).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every configuration, actual trees on its decoded support correspond bijectively to the independent cycle-edge deletion choices.

**Theorem 1.5 (Edges in the pruned graph).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every configuration, deletion choice and pair of vertices, the decoded tree contains the edge exactly when the pruned host contains it and both endpoints belong to the support.

**Theorem 1.6 (Pointwise preservation of tree order).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every tree reconstructed from the deletion choices has the vertex count of its support configuration.

**Definition 1.7 (Choices on a full support).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.fullCycleChoiceEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.fullCycleChoiceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deletion choices on a full vertex support are equivalent to the actual unordered edges of the graph.

**Definition 1.8 (Choices on a proper support).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.properCycleChoiceEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.properCycleChoiceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When a vertex is missing, the choice type is equivalent to a singleton and its unique element deletes no edge.

**Theorem 1.9 (Exact tree multiplicity).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.deletionChoices_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.deletionChoices_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiply a core factor of 5,000 for a full core and one otherwise by a triangle factor of three for a full triangle and one otherwise.

**Definition 1.10 (The deleted unordered vertex pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.deletedEdges`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.deletedEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map the selected local edges to unordered pairs of host vertices and take their union.

**Theorem 1.11 (Every remaining induced edge is forced).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_keeps_edge_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_keeps_edge_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every configuration, deletion choice and pair of vertices, the reconstructed tree contains that pair as an edge exactly when it is a host edge, both endpoints lie in the support and the unordered pair is outside the deleted edge set.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.CycleChoice`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.DeletionChoices`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.TreeFiber`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.deletedEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.deletionChoices_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.fullCycleChoiceEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.properCycleChoiceEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_keeps_edge_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.treeFiberEquiv_order`
- Dependency: [D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement](CambieQ19Settlement.md)
