# The Gallai–Hasse–Roy–Vitaver theorem

## Abstract

A finite simple graph is k-colorable exactly when an orientation bounds every injective directed path by k vertices.

Let V be any finite type in any universe, G a simple undirected graph on V, and k a natural number. Colorable(G,k) means that a proper vertex coloring with values in Fin(k) exists; colors may be unused. No chosen enumeration, decidable adjacency, nonempty vertex set, positive k, connectedness or acyclicity of the input orientation is required. Relations(V) denotes V to V to Prop, and Functions(A,B) denotes the functions from A to B.

**Definition 1.1 (Orientation convention).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall o \in \operatorname{Relations}\left(V\right),\; \operatorname{IsOrientation}\left(G, o\right) \Leftrightarrow \left(\left(\forall a \in V,\; \forall b \in V,\; \operatorname{Adj}\left(G, a, b\right) \Rightarrow \left(\operatorname{o}\left(a, b\right) \lor \operatorname{o}\left(b, a\right)\right)\right) \land \left(\forall a \in V,\; \forall b \in V,\; \operatorname{o}\left(a, b\right) \Rightarrow \operatorname{Adj}\left(G, a, b\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/GallaiRoy.IsOrientation` (`✓ std3`).

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

Every undirected edge must have at least one arc direction, and every arc must be an edge. Both directions on one edge are allowed. Since G has no loops, an orientation has no loops. The word orientation here does not require exactly one direction.

**Definition 1.2 (Paths count vertices).**

$$\forall V \in \mathrm{Type},\; \forall o \in \operatorname{Relations}\left(V\right),\; \forall m \in \mathrm{Nat},\; \forall f \in \operatorname{Functions}\left(\operatorname{Fin}\left(m\right), V\right),\; \operatorname{IsDirectedPath}\left(o, f\right) \Leftrightarrow \left(\operatorname{Injective}\left(f\right) \land \left(\forall i \in \mathrm{Nat},\; i + 1 < m \Rightarrow \operatorname{o}\left(\operatorname{f}\left(i\right), \operatorname{f}\left(i + 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/GallaiRoy.IsDirectedPath` (`✓ std3`).

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

For any natural m, a path is an injective function f from Fin(m) to V such that an arc joins f(i) to f(i+1) whenever i+1 is less than m. The displayed natural indices carry their canonical Fin(m) bounds. The path has m vertices and, when m is positive, m-1 edges. The empty function is a path with zero vertices; every singleton function is a path with one vertex. Neither a closing arc nor a terminal-to-initial equality is imposed.

**Theorem 1.3 (Colorings and bounded-path orientations).**

$$\forall V \in \mathrm{Type},\; \operatorname{Finite}\left(V\right) \Rightarrow \left(\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall k \in \mathrm{Nat},\; \operatorname{Colorable}\left(G, k\right) \Leftrightarrow \left(\exists o \in \operatorname{Relations}\left(V\right),\; \operatorname{IsOrientation}\left(G, o\right) \land \left(\forall m \in \mathrm{Nat},\; \forall f \in \operatorname{Functions}\left(\operatorname{Fin}\left(m\right), V\right),\; \operatorname{IsDirectedPath}\left(o, f\right) \Rightarrow m \le k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/GallaiRoy.colorable_iff_exists_orientation` (`✓ std3`). ∎

*Citation.* Juan Pablo Traverso Gianini (2026). *Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure*. URL: <https://github.com/jtraverso>.

*Commentary.*

For all V, G and k as above, G is k-colorable if and only if there exists a relation o satisfying the orientation convention and bounding every injective directed path by k vertices. The path bound quantifies over every natural m and every f from Fin(m) to V, rather than only paths presented by a selected walk representation.

From a coloring c, orient each edge from its smaller color to its larger color. Properness supplies a direction on every edge. Along a directed path the colors strictly increase, so their composite with f is an injection into Fin(k), giving m at most k.

For the converse choose, among all acyclic subrelations D of o, one maximal under inclusion. Such a relation exists because V is finite and the empty relation is acyclic. Every D-chain is without repetition: a repeated vertex would yield a nonempty D-path back to itself. Thus its underlying list gives an injective o-path, and the assumed bound limits its number of vertices.

For each vertex v let h(v) be the largest number of edges in a D-chain starting at v. The singleton chain exists, and the path bound gives h(v) less than k. Every nonempty D-path from a to b lets one prepend that path to a longest chain from b, so h(b) is strictly less than h(a). If an original arc u to v is absent from D, maximality forces a D-path from v back to u: otherwise adding that arc preserves acyclicity and strictly enlarges D. The added-edge path decomposition verifies this assertion even when a walk traverses the new arc more than once. The endpoints differ because o has no loops, so this return path is nonempty. Their heights again differ. Consequently every original graph edge has unequal endpoint heights, and v mapped to h(v) in Fin(k) is a proper coloring.

Empty V is included for every k, including zero: its empty coloring and empty relation satisfy the statement. For nonempty V, the singleton directed paths force k at least one, so neither side holds at k=0. Reciprocal arcs and directed cycles in o remain within the theorem; acyclicity belongs only to the selected internal subrelation D. The reverse construction happens to produce an acyclic orientation, but the existential statement does not impose that extra condition.

This is the classical Gallai–Hasse–Roy–Vitaver theorem. Roy's Theorem 1 and the sharpness discussion supply the historical mathematical reference. The Lean construction is received from Juan Pablo Traverso Gianini's immutable Lean Pool source; its maximal-acyclic argument is not attributed as Roy's original proof. The source note records exact software attribution and licenses, and identifies the related restricted native-rank application. Roy's stronger Theorem 2 is outside this statement.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/GallaiRoy.IsDirectedPath`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/GallaiRoy.IsOrientation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/GallaiRoy.colorable_iff_exists_orientation`
