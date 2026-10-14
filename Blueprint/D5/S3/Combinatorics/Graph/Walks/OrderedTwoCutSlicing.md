# Two Ordered Cuts of an Actual Graph Path

## Abstract

Two ordered actual path edges determine three endpoint-typed paths with full support and exact retained edges.

The simple graph and vertex type are arbitrary. Positions i and j are actual edge indices of one supplied simple path, with i less than j. Endpoint equalities record its direction through each cut. No abstract three-piece realization or target support certificate is assumed. This supplies the concrete Q slicing used by native recursive graph surgery; it does not assert an all-order Hamilton construction.

**Theorem 1.1 (Cut at the Two Supplied Edge Positions).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/OrderedTwoCutSlicing.exists_path_slicing_at_two_ordered_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/OrderedTwoCutSlicing.exists_path_slicing_at_two_ordered_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist actual paths q0, q1 and q2 whose endpoints are exactly the original endpoints and the four directed cut endpoints. Their support lists concatenate to the original full support. Inserting the two undirected cuts between their edge lists recovers the original edge list; omitting them gives exactly the original edge list filtered to exclude those cuts. The three lengths are i, j-i-1 and the original length minus j minus one. Adjacent cuts are allowed: the middle nil path retains its single vertex. The proof constructs take/drop walks, keeps their endpoint identities by copy, splits the original edge list at the two indices and uses simplicity to exclude every further occurrence of either cut.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/OrderedTwoCutSlicing.exists_path_slicing_at_two_ordered_edges`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
