# Actual cycle transport and matching signs

## Abstract

Actual alternating-cycle flips transport canonical Pfaffian coefficients; odd opposition on actual nice cycles makes all matching coefficients equal.

**Definition 1.1 (The matching equivalence).**

$$\forall n \in \mathbb{N},\; \operatorname{TypeOf}\left(\operatorname{matchingEquiv}\left(n\right)\right) = \operatorname{Equiv}\left(\{M:\operatorname{Subgraph}\left(\operatorname{CompleteGraph}\left(\operatorname{Fin}\left(2 \cdot n\right)\right)\right) \mid \operatorname{IsPerfectMatching}\left(M\right)\}, \operatorname{P}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.matchingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a perfect matching M, matchingMate chooses the unique vertex adjacent to each vertex. Symmetry makes this map involutive; looplessness excludes fixed points. Conversely, a partner map p defines a spanning subgraph by adjacency p(v) = w. Involutivity supplies symmetry, and the partner is the unique neighbor. The two constructions are inverse, including on the empty vertex type. The matching objects are Mathlib SimpleGraph.Subgraph objects, rather than an additional matching datatype.

For an enumeration e from V to Fin(2n), an actual perfect matching is transported to the complete graph and converted by matchingEquiv into its partner map. Its canonical listing c orders each pair increasingly and then orders pairs by their first endpoints. Given actual dart bits epsilon, dartSign(d) is the integer unit (-1) raised to epsilon(d), using the ZMod(2) action on integer units. It equals one at bit zero and minus one at bit one. The reversal hypothesis is epsilon(symm(d)) = 1 + epsilon(d); it implies dartSign(symm(d)) = -dartSign(d). The matching coefficient matchingTau(e,epsilon,M) is sign(c) times the product of these signs on the actual directed matching edges listed by c. Reordering the pairs or reversing individual pairs gives the same signed unit factor.

For any commutative ring R and weights w on the actual undirected edges of G, orientedMatrix(e,epsilon,w) has entry intCast(dartSign(x,y)) times w({x,y}) on an actual edge and zero on nonedges. Its diagonal is explicitly zero, including in characteristic two. matchingWeight(w,M) multiplies over the subtype of actual undirected edges of M; partitionFunction(w) sums these products over actual perfect-matching subgraphs. Empty products are one and empty sums are zero. The nice-cycle hypothesis NiceOdd(epsilon) quantifies over actual simple even closed walks p whose actual vertex-deleted induced complement has an actual perfect matching; it requires the sum of epsilon along p.darts to be one in ZMod(2). These definitions do not assume a common matching sign.

The native FixedPointFreeInvolution carrier consists of involutive fixed-point-free permutations. For each n, a partner map in P(n) becomes such a permutation by Equiv.ofBijective applied to its involutive underlying function; forgetting the permutation structure is the inverse. Both composites preserve the underlying partner function pointwise. Thus the original partner maps and native carrier describe exactly the same pairings, including n = 0. This correspondence concerns the partner action; the Pfaffian coefficient remains the sign of the normalized listing permutation, not the sign of the involutive partner permutation.

**Theorem 1.2 (A flip and its actual complement).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall M \in \operatorname{Subgraph}\left(G\right),\; \forall v \in V,\; \forall p \in \operatorname{Walk}\left(G, v, v\right),\; \operatorname{IsPerfectMatching}\left(M\right) \Rightarrow \left(\operatorname{IsCycle}\left(p\right) \Rightarrow \left(\operatorname{IsAlternating}\left(\operatorname{spanningCoe}\left(\operatorname{toSubgraph}\left(p\right)\right), \operatorname{spanningCoe}\left(M\right)\right) \Rightarrow \left(\operatorname{Even}\left(\operatorname{length}\left(p\right)\right) \land \left(\left(\exists N \in \operatorname{Subgraph}\left(G\right),\; \operatorname{IsPerfectMatching}\left(N\right) \land \left(\forall x \in V,\; \forall y \in V,\; \operatorname{Adj}\left(N, x, y\right) \Leftrightarrow \left(\left(\operatorname{Adj}\left(M, x, y\right) \land \left(\neg \operatorname{Adj}\left(\operatorname{toSubgraph}\left(p\right), x, y\right)\right)\right) \lor \left(\operatorname{Adj}\left(\operatorname{toSubgraph}\left(p\right), x, y\right) \land \left(\neg \operatorname{Adj}\left(M, x, y\right)\right)\right)\right)\right)\right) \land \left(\exists N \in \operatorname{Subgraph}\left(\operatorname{Induce}\left(G, \operatorname{Complement}\left(\operatorname{Verts}\left(\operatorname{toSubgraph}\left(p\right)\right)\right)\right)\right),\; \operatorname{IsPerfectMatching}\left(N\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.alternating_cycle_flip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be any simple graph, M an actual perfect-matching subgraph, and p an actual simple closed walk. Write C for p.toSubgraph and let Alt(C,M) mean that among two distinct edges of C incident to a vertex, precisely one belongs to M. No embedding, connectedness, finiteness, orientation, or weight assumption is required for this statement.

The flipped graph has edge set equal to the symmetric difference of M and C. Its edges are still actual G-edges. Mathlib's perfect-matching symmetric-difference theorem proves that the resulting spanning subgraph is a perfect matching. The displayed adjacency equivalence toggles exactly the cycle edges and preserves all other edges, including shared matching edges outside C.

Every vertex of C has two distinct neighbors in C. Alternation places precisely one of those edges in M. Restricting M to the vertices of C gives a perfect matching there. Those vertices are enumerated injectively by the walk indices before the repeated endpoint. The even-cardinality theorem for actual perfect matchings therefore proves that p has even length. Uniqueness of the matching partner also prevents an M-edge from crossing between the vertices of C and their complement. Restricting the same M to the induced graph on the complementary vertex set gives an actual perfect matching there. The notation Induce(G,Complement(Verts(C))) denotes this graph, with vertices the subtype of original vertices outside C.

The same actual complement matching supplies the nice-cycle premise in the coefficient and uniformity statements below.

**Theorem 1.3 (Transport of the actual coefficient).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall n \in \mathbb{N},\; \forall e \in \operatorname{Equiv}\left(V, \operatorname{Fin}\left(2 \cdot n\right)\right),\; \forall epsilon \in \operatorname{Function}\left(\operatorname{Dart}\left(G\right), \operatorname{ZMod}\left(2\right)\right),\; \forall M \in \operatorname{PM}\left(G\right),\; \forall v \in V,\; \forall p \in \operatorname{Walk}\left(G, v, v\right),\; \operatorname{Reverses}\left(epsilon\right) \Rightarrow \left(\operatorname{IsCycle}\left(p\right) \Rightarrow \left(\operatorname{IsAlternating}\left(\operatorname{spanningCoe}\left(\operatorname{toSubgraph}\left(p\right)\right), \operatorname{spanningCoe}\left(M\right)\right) \Rightarrow \left(\exists N \in \operatorname{PM}\left(G\right),\; \left(\forall x \in V,\; \forall y \in V,\; \operatorname{Adj}\left(N, x, y\right) \Leftrightarrow \left(\left(\operatorname{Adj}\left(M, x, y\right) \land \left(\neg \operatorname{Adj}\left(\operatorname{toSubgraph}\left(p\right), x, y\right)\right)\right) \lor \left(\operatorname{Adj}\left(\operatorname{toSubgraph}\left(p\right), x, y\right) \land \left(\neg \operatorname{Adj}\left(M, x, y\right)\right)\right)\right)\right) \land \operatorname{matchingTau}\left(e, epsilon, M\right) \cdot \operatorname{matchingTau}\left(e, epsilon, N\right) = -\operatorname{Product}\left(\operatorname{Map}\left(\operatorname{dartSign}\left(epsilon\right), \operatorname{darts}\left(p\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.alternating_cycle_transport` (`✓ std3`). ∎

*Citation.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

Let PM(G) denote the subtype of actual perfect-matching subgraphs. For M in PM(G), tau(e,epsilon,M) is matchingTau, the genuine canonical permutation coefficient multiplied by the actual directed-edge signs. The theorem constructs N in PM(G) with exactly the displayed toggle adjacency and proves the coefficient product. It assumes reversal of epsilon and actual alternation, without assuming nice-cycle oddness or equality of matching signs.

Rotate the vertices of p once in walk order and fix every vertex outside p. The simple-cycle condition makes this a permutation. Its support has the even cardinality length(p), so its sign is minus one. Among the two cycle neighbors of each cycle vertex, precisely one is its M-partner. The rotation therefore sends every M-edge on the cycle to the complementary cycle edge. Each outside M-edge has both endpoints outside the cycle and is fixed. Applying this permutation to the canonical listing of M gives a listing of the actual flipped matching N; signed listing normalization identifies its value with tau(e,epsilon,N).

For an M-pair x,y on the cycle, multiply the sign on x,y by the sign on its rotated pair. The result is the product of the forward dart signs at x and y. If the listed pair points backward, reversal negates both factors and leaves their product unchanged. For an outside pair the identical sign occurs twice and its product is one in the integer units. Reindexing over all vertices gives the dart product around p, with the single minus sign contributed by the cycle rotation. The argument preserves a common outside pairing even when its labels interleave with cycle labels. This is the composition-cycle sign relation of Cimasoni and Reshetikhin, Section 5.1, realized here on actual simple-graph subgraphs and walks.

**Theorem 1.4 (Nice cycles force a common sign).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall n \in \mathbb{N},\; \forall e \in \operatorname{Equiv}\left(V, \operatorname{Fin}\left(2 \cdot n\right)\right),\; \forall epsilon \in \operatorname{Function}\left(\operatorname{Dart}\left(G\right), \operatorname{ZMod}\left(2\right)\right),\; \forall M \in \operatorname{PM}\left(G\right),\; \forall N \in \operatorname{PM}\left(G\right),\; \operatorname{Reverses}\left(epsilon\right) \Rightarrow \left(\operatorname{NiceOdd}\left(epsilon\right) \Rightarrow \operatorname{matchingTau}\left(e, epsilon, M\right) = \operatorname{matchingTau}\left(e, epsilon, N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.niceOdd_matching_tau_eq` (`✓ std3`). ∎

*Citation.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For two actual perfect matchings, their spanning symmetric difference has degree zero or two. If it is nonempty, its finite component through a disagreement edge supplies an actual simple cycle. The cycle is alternating with respect to the first matching and lies in the same original graph. Its induced vertex-deleted complement has the perfect matching supplied by that first matching. NiceOdd makes its dart-sign product minus one. The transport relation then makes the coefficients of the matching and its flip equal.

Flipping removes the chosen cycle from the disagreement graph. Its edge set strictly decreases, so induction on the finite number of disagreement edges ends at the second matching. Shared matching edges are outside the disagreement graph throughout. The proof includes disconnected graphs and the case M = N. It requires neither an embedding nor existence of a perfect matching as an extra hypothesis; the statement quantifies over any two that exist.

**Theorem 1.5 (One unit for all weights and coefficient rings).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall n \in \mathbb{N},\; \forall R \in \operatorname{Type}\left(\right),\; [\operatorname{CommRing}\left(R\right)] \forall e \in \operatorname{Equiv}\left(V, \operatorname{Fin}\left(2 \cdot n\right)\right),\; \forall epsilon \in \operatorname{Function}\left(\operatorname{Dart}\left(G\right), \operatorname{ZMod}\left(2\right)\right),\; \forall w \in \operatorname{Function}\left(\operatorname{edgeSet}\left(G\right), R\right),\; \operatorname{Reverses}\left(epsilon\right) \Rightarrow \left(\operatorname{NiceOdd}\left(epsilon\right) \Rightarrow \operatorname{pfaffian}\left(\operatorname{orientedMatrix}\left(e, epsilon, w\right)\right) = \operatorname{IntCast}\left(\operatorname{IntegerValue}\left(\operatorname{orientationUnit}\left(e, epsilon\right)\right)\right) \cdot \operatorname{partitionFunction}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.weighted_pfaffian_identity` (`✓ std3`). ∎

*Citation.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

Use listingEquiv to reindex the independently defined standard sum by the supplied partner maps. A partner map is supported precisely when all its paired vertices are joined by actual G-edges. The supplied complete-graph pairingGraph is pulled back along e with this support proof, giving an actual perfect matching; matchingPairing is its inverse. This reuses the original mate and inverse chain and introduces no second pairing or Pfaffian core.

An unsupported pairing has a zero matrix factor, so its contribution is zero without a nonzero-weight premise. For an actual matching, the canonical pair slots biject with its actual undirected edge subtype. Injectivity follows from distinct permutation slots, and surjectivity follows from uniqueness of the matching partner. Thus its matrix product equals the cast of matchingTau times matchingWeight, with each actual undirected edge counted once. Summing and using the common coefficient proves the displayed formula over an arbitrary CommRing. No division is used.

The coefficient uniformity is supplied by actual alternating-cycle transport and induction on disagreement edges. Consequently the graph, cycle, complement matching, listing and weight factors all belong to the same actual realization. The signed identity permits negative and zero weights, shared matching edges, disconnected graphs and coefficient rings of characteristic two.

For nonnegative real weights, each edge-once matching product is nonnegative, so Z = partitionFunction(w) is nonnegative. Apply the displayed identity at R = Real. The integer value of orientationUnit is one or minus one, hence its real absolute value is one. Multiplicativity of absolute value and abs(Z) = Z give abs(Pf(A(e,epsilon,w))) = Z. This consequence uses precisely the additional hypothesis that every actual edge weight is nonnegative; the signed identity requires no such hypothesis.

When V is empty, the standard sum has one empty pairing and the actual graph has one empty matching, so both values are one. With no perfect matching, every pairing contribution vanishes and the partition sum is empty, so both values are zero. These cases are included in the formula. This conditional algebraic theorem does not construct planar orientations or geometric embeddings, prove the determinant-square identity, introduce square roots, or establish algorithmic complexity or hardness results.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.alternating_cycle_flip`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.alternating_cycle_transport`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.matchingEquiv`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.niceOdd_matching_tau_eq`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian.weighted_pfaffian_identity`
- Dependency: [D5/S0/Certificates/Combinatorics/NormalizedPfaffian](../../../S0/Certificates/Combinatorics/NormalizedPfaffian.md)
