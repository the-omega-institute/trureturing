# Four-Vertex Matchings and Rank Applications

## Abstract

Actual four-vertex perfect matchings are counted by three supported pairings. Applying matrix rank inequalities gives the weighted and binary rank tables and their signed difference.

Vertices are indexed by Fin 4, with indices 0, 1, 2, 3. The three partner maps exchange respectively the pairs 01 and 23, 02 and 13, and 03 and 12. A perfect matching is an actual SimpleGraph.Subgraph satisfying IsPerfectMatching; it includes every vertex and gives each vertex exactly one adjacent partner.

**Definition 1.1 (Three Partner Maps).**

$$\forall j \in \mathrm{Fin}\left(3\right),\; \forall i \in \mathrm{Fin}\left(4\right),\; \mathrm{mate}\left(j, i\right) = \mathrm{Entry}\left(\mathrm{PartnerTable}, j, i\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.mate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PartnerTable has rows (1,0,3,2), (2,3,0,1), and (3,2,1,0). Every row is an involution without a fixed vertex.

**Definition 1.2 (Actual Perfect-Matching Count).**

$$\forall H \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(4\right)\right),\; \mathrm{pmCount}\left(H\right) = \mathrm{card}\left(\mathrm{PerfectMatchingSubgraphs}\left(H\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.pmCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PerfectMatchingSubgraphs(H) is the subtype of all subgraphs M of H with M.IsPerfectMatching. Its cardinality is Nat.card of this finite type.

**Theorem 1.3 (Exact Matching Objects and Count).**

$$\forall H \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(4\right)\right),\; (\forall M \in \mathrm{Subgraph}\left(H\right),\; (\mathrm{IsPerfectMatching}\left(M\right)) \Leftrightarrow (\exists j \in \mathrm{Fin}\left(3\right),\; (\forall i \in \mathrm{Fin}\left(4\right),\; \mathrm{Adj}\left(H, i, \mathrm{mate}\left(j, i\right)\right)) \land (\forall i \in \mathrm{Fin}\left(4\right),\; \forall k \in \mathrm{Fin}\left(4\right),\; (\mathrm{Adj}\left(M, i, k\right)) \Leftrightarrow (\mathrm{mate}\left(j, i\right) = k)))) \land (\mathrm{pmCount}\left(H\right) = \mathrm{indicator}\left((\mathrm{Adj}\left(H, 0, 1\right)) \land (\mathrm{Adj}\left(H, 2, 3\right))\right)+\mathrm{indicator}\left((\mathrm{Adj}\left(H, 0, 2\right)) \land (\mathrm{Adj}\left(H, 1, 3\right))\right)+\mathrm{indicator}\left((\mathrm{Adj}\left(H, 0, 3\right)) \land (\mathrm{Adj}\left(H, 1, 2\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.actual_matching_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the unique partner of vertex 0. It is 1, 2, or 3. Symmetry fixes its partner as 0. The two remaining vertices must be paired with each other, because the already paired vertices cannot acquire a second partner. Conversely, each of the three pairings gives a perfect-matching subgraph exactly when both of its edges occur in H. The public equivalence ranges over every actual subgraph M of H: M is a perfect matching if and only if its adjacency relation is one of the three supported partner maps. Support means that H contains every prescribed partner edge. Because every vertex has a partner, these subgraphs also have the full vertex set; no isolated-vertex choices remain. The constructions form a bijection, so their supported indicators sum to the actual cardinality. Each indicator is 1 when its two edges occur and 0 otherwise.

## Parameters of the Rank Application

The public theorem above identifies matching objects and counts them. The following rank and graph consequences are applications of actual_matching_count and the matrix results named below. They recover Proposition 4.2 of the stabilizer multientropy masked-rank correction theory under the correspondence sending its vertex labels 1, 2, 3, 4 to Fin 4 indices 0, 1, 2, 3; its matrix A is the matrix W here.

Let H be any simple graph on Fin 4. Let K be any field of characteristic two and let lambda be an injective function from Fin 4 to K. Injectivity says exactly that the four labels are pairwise distinct; one label may be zero. No nonzero-label or invertible diagonal-label assumption is needed. Define the natural number p and the matrices W over K and B over ZMod 2 by

$$
p = \mathrm{pmCount}\left(H\right)
$$

$$
\forall i \in \mathrm{Fin}\left(4\right),\; \forall j \in \mathrm{Fin}\left(4\right),\; \mathrm{Entry}\left(W, i, j\right) = \begin{cases}\mathrm{lambda}\left(i\right) + \mathrm{lambda}\left(j\right)&\mathrm{Adj}\left(H, i, j\right)\\0&\operatorname{otherwise}\end{cases}
$$

$$
B = \mathrm{adjMatrix}\left(\mathrm{ZMod}\left(2\right), H\right)
$$

B is defined independently: an edge has entry 1 and a nonedge has entry 0. It does not require four distinct labels in ZMod 2, and is not obtained by specializing lambda to that field. Both matrices are symmetric with zero diagonal. Write E for the assertion that H has at least one edge:

$$
(E) \Leftrightarrow (\exists i \in \mathrm{Fin}\left(4\right),\; \exists j \in \mathrm{Fin}\left(4\right),\; \mathrm{Adj}\left(H, i, j\right))
$$

## Pairing Weights and Support

Index the three pairings by 0, 1, 2 in the order 01 with 23, 02 with 13, and 03 with 12. Let q at each index be 1 when both edges of that pairing occur in H, and 0 otherwise. The count component (actual_matching_count H).2 gives p as their sum; its first component ensures that this counts actual perfect-matching subgraphs, rather than a separately chosen pairing count.

$$
p = q_{0} + q_{1} + q_{2}
$$

$$
p \in \left\{0, 1, 2, 3\right\}
$$

Define the three complete-pairing weights, whether or not their edges occur in H. These indices correspond to the original omega indices 1, 2, 3:

$$
\omega_{0} = \left(\mathrm{lambda}\left(0\right) + \mathrm{lambda}\left(1\right)\right) \cdot \left(\mathrm{lambda}\left(2\right) + \mathrm{lambda}\left(3\right)\right)
$$

$$
\omega_{1} = \left(\mathrm{lambda}\left(0\right) + \mathrm{lambda}\left(2\right)\right) \cdot \left(\mathrm{lambda}\left(1\right) + \mathrm{lambda}\left(3\right)\right)
$$

$$
\omega_{2} = \left(\mathrm{lambda}\left(0\right) + \mathrm{lambda}\left(3\right)\right) \cdot \left(\mathrm{lambda}\left(1\right) + \mathrm{lambda}\left(2\right)\right)
$$

$$
(\forall j \in \mathrm{Fin}\left(3\right),\; \omega_{j} \ne 0) \land (\omega_{0} + \omega_{1} + \omega_{2} = 0)
$$

In characteristic two, the sum of two distinct labels cannot be zero, so each factor and each pairing weight is nonzero. Expanding the three products, each product of two different labels occurs twice. Those terms cancel, giving the zero-sum identity. This identity is independent of H; edge support determines which of the three weights contribute.

## From Pairing Sums to Rank

For either coefficient field, write a symmetric zero-diagonal matrix M and its complementary matrix C as follows. The six entries a, b, c, d, e, f are respectively the entries on 01, 02, 03, 12, 13, 23; C moves each entry to the opposite pair of vertices.

$$
M = \begin{bmatrix}0&a&b&c\\a&0&d&e\\b&d&0&f\\c&e&f&0\end{bmatrix}
$$

$$
C = \begin{bmatrix}0&f&e&d\\f&0&c&b\\e&c&0&a\\d&b&a&0\end{bmatrix}
$$

$$
t = a \cdot f + b \cdot e + c \cdot d
$$

$$
(M \cdot C = t \cdot I) \land (C \cdot M = t \cdot I)
$$

Here I is the four-dimensional identity matrix. Multiplication gives t on every diagonal entry; every off-diagonal entry is a sum of two equal products and vanishes in characteristic two. If t is nonzero, Matrix.rank_diagonal gives rank 4 for tI. Matrix.rank_mul_le_left and Matrix.rank_le_width then give rank 4 for M.

If t is zero, Matrix.rank_add_rank_le_card_of_mul_eq_zero gives the next inequality. If M has a nonzero entry x on an edge, its principal two-by-two submatrix has diagonal zero and both off-diagonal entries x. Matrix.det_fin_two gives determinant minus x squared, equal to x squared in characteristic two, hence nonzero. Matrix.rank_of_det_ne_zero and Matrix.rank_submatrix_le give rank at least 2. The corresponding opposite pair in C gives the same lower bound for C, so the inequality forces rank 2 for M. If M is zero, Matrix.rank_zero gives rank 0.

$$
\mathrm{rank}\left(M\right) + \mathrm{rank}\left(C\right) \le 4
$$

For W, t is the sum of the supported pairing weights. For p equal to 0 or 3 this sum is zero. For p equal to 1 it is one nonzero weight. For p equal to 2 it equals the omitted third weight by the zero-sum identity, and is again nonzero. For B, each supported pairing contributes 1, so t is the image of p in ZMod 2: it is nonzero exactly for p equal to 1 or 3. An edge gives a nonzero entry in both W and B; when there are no edges both are zero. These are applications of the named Mathlib matrix results to the actual count, with only finite product expansion and characteristic-two cancellation between them.

## Weighted and Binary Rank Tables

With the parameters and E fixed above, the two tables are

$$
\mathrm{rank}\left(W\right) = \begin{cases}4&(p = 1) \lor (p = 2)\\2&((p = 0) \lor (p = 3)) \land (E)\\0&\neg(E)\end{cases}
$$

$$
\mathrm{rank}\left(B\right) = \begin{cases}4&(p = 1) \lor (p = 3)\\2&((p = 0) \lor (p = 2)) \land (E)\\0&\neg(E)\end{cases}
$$

Ranks here are Matrix.rank, natural numbers computed over the matrix's own field. The rows exhaust all graphs because p is between 0 and 3, and a supported perfect matching supplies edges. In particular, p equal to 0 alone does not distinguish rank 2 from rank 0; edge existence makes that distinction. The binary table holds for every H without any assumption on K or lambda.

## Classification of the Entire Graph

Two distinct supported pairings have no common edge, and their union is a four-cycle. The two remaining edges form the third pairing. If p is 2, either zero or one of the remaining edges can be present: including both would support the third pairing. Thus the entire graph is a four-cycle or a four-cycle with one diagonal, the diamond. Conversely, each of these entire graphs supports exactly two pairings. If p is 3, all three pairings occur, and their six edges exhaust the complete graph. This gives both directions of the following equivalences:

$$
(p = 2) \Leftrightarrow ((\exists e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(4\right), \mathrm{Fin}\left(4\right)\right),\; \forall u \in \mathrm{Fin}\left(4\right),\; \forall v \in \mathrm{Fin}\left(4\right),\; (\mathrm{Adj}\left(H, \mathrm{e}\left(u\right), \mathrm{e}\left(v\right)\right)) \Leftrightarrow (\mathrm{Adj}\left(\mathrm{cycleGraph}\left(4\right), u, v\right))) \lor (\exists e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(4\right), \mathrm{Fin}\left(4\right)\right),\; \forall u \in \mathrm{Fin}\left(4\right),\; \forall v \in \mathrm{Fin}\left(4\right),\; (\mathrm{Adj}\left(H, \mathrm{e}\left(u\right), \mathrm{e}\left(v\right)\right)) \Leftrightarrow (\mathrm{Adj}\left(\mathrm{deleteEdges}\left(\mathrm{completeGraph}\left(\mathrm{Fin}\left(4\right)\right), \mathrm{edge}\left(0, 2\right)\right), u, v\right))))
$$

$$
(p = 3) \Leftrightarrow (H = \mathrm{completeGraph}\left(\mathrm{Fin}\left(4\right)\right))
$$

In the first formula, deleteEdges denotes removal of the undirected edge 02, exactly the graph (top minus SimpleGraph.edge 0 2); this is a fixed representative of the diamond. Each quantified equivalence e is a permutation of all four vertices, and adjacency is preserved and reflected for every ordered pair. The classification is up to isomorphism of the entire graph, not containment of a cycle or diamond inside a larger graph. The complete-graph clause is literal graph equality. Both clauses hold for arbitrary H, including the edgeless graph, without an edge-existence hypothesis.

## Signed Rank Difference and Scope

Convert each natural-number rank separately to Int and then subtract. Subtracting the two tables gives

$$
\mathrm{IntCast}\left(\mathrm{rank}\left(W\right)\right) - \mathrm{IntCast}\left(\mathrm{rank}\left(B\right)\right) = \begin{cases}2&p = 2\\-2&H = \mathrm{completeGraph}\left(\mathrm{Fin}\left(4\right)\right)\\0&\operatorname{otherwise}\end{cases}
$$

IntCast denotes the natural-number cast to Int. For a four-cycle or diamond the ranks are 4 and 2; for the complete graph they are 2 and 4. With p equal to 1 both ranks are 4. With p equal to 0 and an edge both ranks are 2, and for the edgeless graph both are 0. Thus the difference is positive exactly on the two entire-graph isomorphism types in the p equal to 2 clause, negative exactly on the complete graph, and zero in every other case. A cast after natural-number subtraction would lose the negative value.

The weighted table and the signed difference require all four labels to be distinct in a characteristic-two field. They do not assert the same values for repeated labels, other characteristics, arbitrary edge weights, or more vertices. The binary table and the graph classification require only the four-vertex graph. These are algebraic and graph-theoretic consequences of the matching count and the cited matrix inequalities; they assert no physical realization, computational resource bound, or literature novelty.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.actual_matching_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.mate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FourVertexRank.pmCount`
