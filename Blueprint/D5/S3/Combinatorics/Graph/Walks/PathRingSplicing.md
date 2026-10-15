# Splicing Actual Paths around a Ring

## Abstract

Actual graph pieces with independent full support and real connecting edges splice into one Hamilton cycle with exact vertex and edge inventories.

Let G be a simple graph on a type V with decidable equality. A Piece(G) has a start, a finish and an actual G-walk between them. Choose a first piece p and a list ps of subsequent pieces. The list is Linked when each piece's finish is adjacent in G to the next piece's start. The function finish(p,ps) is the finish of the final piece. Write flatMapSupport(p,ps) for the concatenation of all full piece supports. The list chainEdges(p,ps) contains all original piece edges, in order, with exactly one actual connecting edge inserted between consecutive pieces.

**Theorem 1.1 (Every Chain Edge Has an Actual Piece or Consecutive Seam Owner).**

$$\forall V \in \mathrm{Type},\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall p \in \mathrm{Piece}\left(G\right),\; \forall ps \in \mathrm{List}\left(\mathrm{Piece}\left(G\right)\right),\; \forall e \in \mathrm{Sym2Type}\left(V\right),\; e \in \mathrm{chainEdges}\left(p, ps\right) \Rightarrow \left(\left(\exists r \in \mathrm{Piece}\left(G\right),\; r \in \mathrm{cons}\left(p, ps\right) \land e \in \mathrm{edges}\left(\mathrm{walk}\left(r\right)\right)\right) \lor \left(\exists i \in \mathrm{Nat},\; \mathrm{add}\left(i, 1\right) < \mathrm{length}\left(\mathrm{cons}\left(p, ps\right)\right) \land e = \mathrm{Sym2}\left(\mathrm{finish}\left(\mathrm{get}\left(\mathrm{cons}\left(p, ps\right), i\right)\right), \mathrm{start}\left(\mathrm{get}\left(\mathrm{cons}\left(p, ps\right), \mathrm{add}\left(i, 1\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/PathRingSplicing.chain_edge_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every edge in the literal chainEdges list belongs to an actual indexed piece or is the connection between two consecutive actual pieces. Recursive list membership earns the exhaustive classification, including the exact natural index and its successor bound. No support partition, adjacency or equality decision assumption is needed. The full native T/E surgery inventories consume this classification to prove that no additional edges occur.

**Theorem 1.2 (One Actual Hamilton Cycle with Literal Inventories).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall p \in \mathrm{Piece}\left(G\right),\; \forall ps \in \mathrm{List}\left(\mathrm{Piece}\left(G\right)\right),\; \left(\mathrm{Linked}\left(p, ps\right) \land \left(\mathrm{Adj}\left(G, \mathrm{finish}\left(p, ps\right), \mathrm{start}\left(p\right)\right) \land \left(\left(\forall v \in V,\; \mathrm{count}\left(v, \mathrm{flatMapSupport}\left(p, ps\right)\right) = 1\right) \land 3 \le \mathrm{length}\left(\mathrm{flatMapSupport}\left(p, ps\right)\right)\right)\right)\right) \Rightarrow \left(\exists c \in \mathrm{Walk}\left(G, \mathrm{start}\left(p\right), \mathrm{start}\left(p\right)\right),\; \mathrm{IsHamiltonianCycle}\left(c\right) \land \left(\mathrm{tail}\left(\mathrm{support}\left(c\right)\right) = \mathrm{reverse}\left(\mathrm{flatMapSupport}\left(p, ps\right)\right) \land \mathrm{edges}\left(c\right) = \mathrm{cons}\left(\mathrm{Sym2}\left(\mathrm{start}\left(p\right), \mathrm{finish}\left(p, ps\right)\right), \mathrm{reverse}\left(\mathrm{chainEdges}\left(p, ps\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/PathRingSplicing.exists_spliced_hamiltonian_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the list is Linked, its final finish is adjacent to the first start, every vertex of V occurs exactly once in flatMapSupport(p,ps), and that list has at least three entries. There is an actual Hamilton cycle c based at the first start. Its support with the first entry removed equals the reverse of flatMapSupport(p,ps). Its edge list is the real closing edge followed by the reverse of chainEdges(p,ps). No candidate cycle, endpoint pairing or connectedness hypothesis is assumed.

Recursively append each piece, its real connection, and the recursively joined remaining pieces. The vertex at a connection is already the next piece's start, so the full support is exactly the concatenation of the independent piece supports. A second induction preserves the literal edge list. The support counts then make the joined walk Hamiltonian and simple. Reverse it and prepend the supplied closing edge. A closing edge already present in a simple path would force the path to have length one; at least three support entries exclude this. Thus the actual return creates a cycle and its tail contains every vertex exactly once.

For a native switching construction, the separate mathematical obligations are to obtain the actual pieces, prove their complete independent support partition, and verify every specified connection as a real generator edge. This theorem then constructs the full cycle without a Hamiltonian search.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PathRingSplicing.chain_edge_cases`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/PathRingSplicing.exists_spliced_hamiltonian_cycle`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
