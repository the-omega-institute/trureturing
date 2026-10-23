# Complete Recursive Port Boundary Paths

## Abstract

The independently specified even and odd port matchings, together with internal seams, admit complete Hamilton paths and enumerate every matching edge exactly once.

For k at least two, the port set is Fin(k+1) times Fin(2). Write R_i=(i,0) and L_i=(i,1). The graph uses the even matching E_k when k is even and the odd matching O_k when k is odd, together with seams L_i--R_(i+1) for 0<=i<k. The matchings are specified independently of the proposed trace. The empty ladder ranges at k=2 and k=3 are guarded explicitly; neither a connectivity nor a coverage hypothesis is assumed.

**Theorem 1.1 (The Complete Even Trace).**

$$\forall s \in \mathrm{Nat},\; \exists w \in \mathrm{Walk}\left(\mathrm{boundaryGraph}\left(2 \cdot s + 2\right), \mathrm{R}\left(0\right), \mathrm{L}\left(2 \cdot s + 2\right)\right),\; \mathrm{IsHamiltonian}\left(w\right) \land \mathrm{support}\left(w\right) = \mathrm{evenTrace}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary.even_boundary_hamiltonian_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At k=2s+2, evenRoute first visits the even ladder, then the four middle ports, and finally the odd ladder. Its explicit inverse proves both injection and surjection onto the whole port set. Consecutive even-index steps are independently specified matching edges; consecutive odd-index steps are seams. Constructing the actual SimpleGraph walk from this list gives a Hamilton path with exactly evenTrace as support.

**Theorem 1.2 (The Complete Odd Trace).**

$$\forall s \in \mathrm{Nat},\; \exists w \in \mathrm{Walk}\left(\mathrm{boundaryGraph}\left(2 \cdot s + 3\right), \mathrm{R}\left(0\right), \mathrm{L}\left(2 \cdot s + 3\right)\right),\; \mathrm{IsHamiltonian}\left(w\right) \land \mathrm{support}\left(w\right) = \mathrm{oddTrace}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary.odd_boundary_hamiltonian_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At k=2s+3, oddRoute has the analogous ladders, middle ports and a four-port tail. The explicit inverse includes the smallest case s=0, where the ladders are empty. The same support construction proves a Hamilton path with exactly oddTrace as support.

The two literal constructions cover every k>=2 by parity. Both start at R_0 and finish at L_k. This statement is the consequence of the two trace theorems with k=2s+2 or k=2s+3.

**Theorem 1.3 (Every Even Matching Piece Once).**

$$\forall s \in \mathrm{Nat},\; \forall p \in \mathrm{Port}\left(2 \cdot s + 2\right),\; \forall q \in \mathrm{Port}\left(2 \cdot s + 2\right),\; \mathrm{evenBoundary}\left(2 \cdot s + 2, \mathrm{code}\left(p\right), \mathrm{code}\left(q\right)\right) \Rightarrow \left(\exists i \in \mathrm{Fin}\left(2 \cdot s + 3\right),\; \mathrm{Sym2}\left(p, q\right) = \mathrm{evenBEdge}\left(s, i\right) \land \left(\forall j \in \mathrm{Fin}\left(2 \cdot s + 3\right),\; \mathrm{Sym2}\left(p, q\right) = \mathrm{evenBEdge}\left(s, j\right) \Rightarrow j = i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary.even_boundary_edges_once` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every independently specified matching edge equals exactly one unordered pair of consecutive ports at an even trace index. The conclusion retains the whole edge, its unique piece index and its orientation-free equality.

**Theorem 1.4 (Every Odd Matching Piece Once).**

$$\forall s \in \mathrm{Nat},\; \forall p \in \mathrm{Port}\left(2 \cdot s + 3\right),\; \forall q \in \mathrm{Port}\left(2 \cdot s + 3\right),\; \mathrm{oddBoundary}\left(2 \cdot s + 3, \mathrm{code}\left(p\right), \mathrm{code}\left(q\right)\right) \Rightarrow \left(\exists i \in \mathrm{Fin}\left(2 \cdot s + 4\right),\; \mathrm{Sym2}\left(p, q\right) = \mathrm{oddBEdge}\left(s, i\right) \land \left(\forall j \in \mathrm{Fin}\left(2 \cdot s + 4\right),\; \mathrm{Sym2}\left(p, q\right) = \mathrm{oddBEdge}\left(s, j\right) \Rightarrow j = i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary.odd_boundary_edges_once` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every independently specified matching edge equals exactly one unordered pair of consecutive ports at an even trace index. The conclusion retains the whole edge, its unique piece index and its orientation-free equality.

The matching-edge conclusions are stronger than endpoint coverage: for every edge of E_k or O_k there is a unique even-index trace pair representing that unordered edge. Injection of the trace excludes repetition, while uniqueness of each port's matching partner proves exhaustion. Consequently previously earned path pieces may be reordered and reversed according to this trace without losing or duplicating a piece.

This is the symbolic boundary skeleton used in the recursive Big-3 construction. A native permutation-graph consumer must still prove full disjoint child-domain coverage, realize these matching edges by actual sliced walks, and supply the actual c seams. This result alone does not assert a Hamilton cycle in every native graph. The matching patterns and trace follow the repository's Big-3 two-a-cut repair, equations (58.22)--(58.23) and section 58.9; no literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary.even_boundary_edges_once`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary.even_boundary_hamiltonian_path`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary.odd_boundary_edges_once`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary.odd_boundary_hamiltonian_path`
