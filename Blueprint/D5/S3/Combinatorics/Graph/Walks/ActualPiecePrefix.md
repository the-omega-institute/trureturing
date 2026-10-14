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

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_second_edge_cut_of_prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.actual_two_retained_edges_force_prefix`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
