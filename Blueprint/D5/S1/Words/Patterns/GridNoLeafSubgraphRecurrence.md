# No-Leaf Subgraphs of the Three-by-n Grid

## Abstract

Barker's recurrence and Kagey's modulo-ten congruence for no-leaf subgraphs of the three-by-n grid.

Vertices are pairs in Fin(3) times Fin(n). An Edge(n) value records its lower or left column and one of five labels. Labels zero and one are the two vertical edges in that column; labels two, three, and four are the horizontal edges in rows zero, one, and two. Horizontal labels are absent in the final column.

A selected edge set is spanning because all vertices remain in the graph. NoLeaf permits isolated vertices and excludes exactly the vertices of degree one. The sequence a counts all selected edge sets satisfying that condition.

**Definition 1.1 (Canonical grid-edge labels).**

$$\forall n \in N,\; Edge\left(n\right) = \{p: Fin\left(n\right) \times Fin\left(5\right) \mid val\left(snd\left(p\right)\right) < 2 \lor val\left(fst\left(p\right)\right) + 1 < n\}$$

*Formalization.* `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.Edge` (`✓ std3`).

*Citation.* Peter Kagey; Colin Barker (2018). *OEIS A301976, Number of no-leaf subgraphs of the 3 X n grid*. URL: <https://oeis.org/A301976>.

*Commentary.*

This is the literal subtype of column-label pairs satisfying the vertical or horizontal validity condition.

**Definition 1.2 (The edge labels form a finite type).**

$$\forall n \in N,\; Fintype\left(Edge\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.instFintypeEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The instance uses the filtered universe of Fin(n) times Fin(5); its members are exactly the values of Edge(n).

**Definition 1.3 (The complete grid-edge set).**

$$\forall n \in N,\; gridEdges\left(n\right) = univ\left(Edge\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.gridEdges` (`✓ std3`).

*Citation.* Peter Kagey; Colin Barker (2018). *OEIS A301976, Number of no-leaf subgraphs of the 3 X n grid*. URL: <https://oeis.org/A301976>.

*Commentary.*

The complete edge set is the finite universe of Edge(n).

**Definition 1.4 (Incident selected-edge count).**

$$\forall n \in N, H \in Finset\left(Edge\left(n\right)\right), x \in Fin\left(3\right) \times Fin\left(n\right),\; degree\left(H, x\right) = card\left(filter\left((e \mapsto if\left(val\left(snd\left(val\left(e\right)\right)\right) < 2, (x = pair\left(val\left(snd\left(val\left(e\right)\right)\right), fst\left(val\left(e\right)\right)\right) \lor x = pair\left(val\left(snd\left(val\left(e\right)\right)\right) + 1, fst\left(val\left(e\right)\right)\right)), (x = pair\left(val\left(snd\left(val\left(e\right)\right)\right) - 2, fst\left(val\left(e\right)\right)\right) \lor x = pair\left(val\left(snd\left(val\left(e\right)\right)\right) - 2, val\left(fst\left(val\left(e\right)\right)\right) + 1\right))\right)), H\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.degree` (`✓ std3`).

*Citation.* Peter Kagey; Colin Barker (2018). *OEIS A301976, Number of no-leaf subgraphs of the 3 X n grid*. URL: <https://oeis.org/A301976>.

*Commentary.*

The predicate is written directly from the five edge labels. Vertical label k joins rows k and k+1 in its column. Horizontal label k joins row k-2 in its recorded column to the next column.

**Definition 1.5 (No vertex has degree one).**

$$\forall n \in N, H \in Finset\left(Edge\left(n\right)\right),\; NoLeaf\left(H\right) \Leftrightarrow (\forall x \in Fin\left(3\right) \times Fin\left(n\right),\; degree\left(H, x\right) \ne 1)$$

*Formalization.* `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.NoLeaf` (`✓ std3`).

*Citation.* Peter Kagey; Colin Barker (2018). *OEIS A301976, Number of no-leaf subgraphs of the 3 X n grid*. URL: <https://oeis.org/A301976>.

*Commentary.*

The predicate ranges over every vertex in Fin(3) times Fin(n); degree zero is allowed.

**Definition 1.6 (The no-leaf subgraph count).**

$$\forall n \in N,\; a\left(n\right) = card\left(filter\left((H \mapsto NoLeaf\left(H\right)), powerset\left(gridEdges\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.a` (`✓ std3`).

*Citation.* Peter Kagey; Colin Barker (2018). *OEIS A301976, Number of no-leaf subgraphs of the 3 X n grid*. URL: <https://oeis.org/A301976>.

*Commentary.*

The powerset ranges over all spanning edge-subgraphs, and the filter retains exactly those satisfying NoLeaf.

**Theorem 1.7 (Barker's order-four recurrence).**

$$\forall n \in N,\; 4 < n \Rightarrow int\left(a\left(n\right)\right) = 12 \cdot int\left(a\left(n - 1\right)\right) - 6 \cdot int\left(a\left(n - 2\right)\right) - 20 \cdot int\left(a\left(n - 3\right)\right) - 5 \cdot int\left(a\left(n - 4\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.barker_a301976` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a301976-grid-no-leaf-recurrence` (proved) by `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.barker_a301976`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a301976-grid-no-leaf-recurrence","declaration_gid":"D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.barker_a301976","resolution_kind":"proved"} -->

*Citation.* Peter Kagey; Colin Barker (2018). *OEIS A301976, Number of no-leaf subgraphs of the 3 X n grid*. URL: <https://oeis.org/A301976>.

*Commentary.*

A bijection sends edge sets to compatible column-mask paths. Their eight-state transfer recurrence satisfies the displayed order-four identity, which gives the result after the path count is identified with a(n).

**Theorem 1.8 (Kagey's modulo-ten congruence).**

$$\forall n \in N,\; 2 < n \Rightarrow a\left(n\right) \bmod 10 = 3$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.kagey_a301976_mod10` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a301976-grid-no-leaf-mod-ten` (proved) by `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.kagey_a301976_mod10`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a301976-grid-no-leaf-mod-ten","declaration_gid":"D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.kagey_a301976_mod10","resolution_kind":"proved"} -->

*Citation.* Peter Kagey; Colin Barker (2018). *OEIS A301976, Number of no-leaf subgraphs of the 3 X n grid*. URL: <https://oeis.org/A301976>.

*Commentary.*

The initial residues at indices three through six are three. Strong induction then applies Barker's recurrence modulo ten.

## References

- Truth anchor: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.Edge`
- Truth anchor: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.NoLeaf`
- Truth anchor: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.a`
- Truth anchor: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.barker_a301976`
- Truth anchor: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.degree`
- Truth anchor: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.gridEdges`
- Truth anchor: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.instFintypeEdge`
- Truth anchor: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.kagey_a301976_mod10`
