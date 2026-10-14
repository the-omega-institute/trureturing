# Cutting the Forced Prefix of an Actual Graph Path

## Abstract

Two retained start edges force a literal actual path prefix and an exact second-edge cut.

The vertex type and simple graph are arbitrary. A Piece records its actual walk and both actual endpoints. Full support lists retain every vertex; Sym2 edges forget orientation. These generic statements supply the local slicing and endpoint steps used in recursive native graph surgery. They do not themselves assert a recursively constructed Hamilton cycle for all orders.

**Theorem 1.1 (Two Edges Force the Literal Prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_two_retained_edges_force_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_two_retained_edges_force_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be an actual simple path from a to b with edges {a,x} and {x,y}, and assume y differs from a. Then actual adjacencies a-x and x-y and a simple tail q from y to b exist, with p literally equal to their two cons steps followed by q. Its support equals a :: x :: support(q), and its edges equal {a,x} :: {x,y} :: edges(q). Starting-edge uniqueness is applied twice to the actual path; y differs from a to exclude identifying the two undirected edges.

**Theorem 1.2 (Cut the Forced Second Edge).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_second_edge_cut_of_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_second_edge_cut_of_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under those same hypotheses, actual simple paths p0 from a to x and p1 from y to b exist. The first has length one. Their full supports concatenate to the original support; their edges, with {x,y} inserted between them, equal the original edge list. Without that cut their edges equal the original list filtered to exclude {x,y}. Simplicity rules out any further occurrence of the cut.

**Theorem 1.3 (An Incident Edge Belongs to the Unique Actual Piece).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_partition_incident_edge_owner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_partition_incident_edge_owner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a list of pieces whose full supports contain no repeated vertex, an edge from the global inventory incident to a vertex of one supplied piece must belong to that same piece. This recovers local edge ownership from the actual global vertex partition.

**Theorem 1.4 (Recover a Prefix from the Global Retained Inventory).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_piece_prefix_from_retained_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_piece_prefix_from_retained_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual simple piece in such a vertex partition, two retained global edges beginning at its literal start force its literal two-step prefix, provided the second endpoint differs from the start. Global ownership is proved before the local prefix construction is applied.

**Theorem 1.5 (Recover the Actual Two-Step Suffix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_piece_suffix_from_retained_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_piece_suffix_from_retained_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding retained edges incident to the literal finish force a two-step suffix of the supplied piece. The proof reverses that actual path, recovers the prefix there and reverses the constructed walk; it keeps the original endpoints.

**Theorem 1.6 (Locate the Directed Cut in the Actual Path).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_retained_suffix_cut_position`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_retained_suffix_cut_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given two distinct retained suffix edges of a supplied actual simple path, an actual edge index exists whose getVert values give the required directed cut. Its index lies within the original path length. This supplies a concrete cut position for the subsequent ordered slicing proof.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_partition_incident_edge_owner`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_piece_prefix_from_retained_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_piece_suffix_from_retained_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_retained_suffix_cut_position`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_second_edge_cut_of_prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_two_retained_edges_force_prefix`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
