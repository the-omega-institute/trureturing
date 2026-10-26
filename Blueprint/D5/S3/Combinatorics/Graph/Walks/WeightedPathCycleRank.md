# Ranks of Weighted Paths and Cycles

## Abstract

Ranks of Weighted Paths and Cycles

Let V be any finite vertex type and K any characteristic-two field. All matrices retain their actual entries; symmetry, zero diagonal and exact graph support express an alternating matrix. Equivalences carry arbitrary vertex labels. A path has every size m, including m=1 and m=2. An odd cycle has every odd m>=3. The graph evenCycleGraph(n) has two copies of Fin(n+2), with edges L(i)-R(i) and L(i)-R(sigma(i)); its two displayed edge families are the two alternating perfect matchings, each covering every vertex exactly once. WeightedCycleWalk.parityIso identifies it with the ordinary cycle on 2(n+2) vertices, hence this covers every even length at least four.

**Theorem 1.1 (Every weighted path).**

$$\forall V \in Type,\; [\mathrm{Fintype}\left(V\right)] \forall K \in Type,\; [\mathrm{Field}\left(K\right)] [\mathrm{CharP}\left(K, 2\right)] \forall m \in \mathrm{Nat},\; \forall A \in \mathrm{Matrix}\left(V, V, K\right),\; \forall e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(m\right), V\right),\; ((\mathrm{IsSymm}\left(A\right)) \land \left((\forall i \in V,\; A\left(i\right)\left(i\right) = 0) \land \left(\forall i \in \mathrm{Fin}\left(m\right),\; \forall j \in \mathrm{Fin}\left(m\right),\; (\mathrm{Adj}\left(\mathrm{pathGraph}\left(m\right), i, j\right)) \Leftrightarrow A\left(e\left(i\right)\right)\left(e\left(j\right)\right) \ne 0\right)\right)) \Rightarrow \mathrm{rank}\left(A\right) = 2 \cdot \mathrm{NatDiv}\left(m, 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the support is the path on m vertices, rank(A)=2 floor(m/2). NoEvenCycleRank.rank_eq_twice_maximum_matching is applied directly. Pairing consecutive vertices constructs a matching of floor(m/2) edges, and the vertex count bounds every matching above by this number. No restriction is imposed on the nonzero edge weights.

**Theorem 1.2 (Every weighted odd cycle).**

$$\forall V \in Type,\; [\mathrm{Fintype}\left(V\right)] \forall K \in Type,\; [\mathrm{Field}\left(K\right)] [\mathrm{CharP}\left(K, 2\right)] \forall m \in \mathrm{Nat},\; \forall A \in \mathrm{Matrix}\left(V, V, K\right),\; \forall e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(m\right), V\right),\; ((3 \le m) \land \left((\mathrm{Odd}\left(m\right)) \land \left((\mathrm{IsSymm}\left(A\right)) \land \left((\forall i \in V,\; A\left(i\right)\left(i\right) = 0) \land \left(\forall i \in \mathrm{Fin}\left(m\right),\; \forall j \in \mathrm{Fin}\left(m\right),\; (\mathrm{Adj}\left(\mathrm{cycleGraph}\left(m\right), i, j\right)) \Leftrightarrow A\left(e\left(i\right)\right)\left(e\left(j\right)\right) \ne 0\right)\right)\right)\right)) \Rightarrow \mathrm{rank}\left(A\right) = m - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_odd_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For odd m>=3 and exact cycle support, rank(A)=m-1. Connectedness and degree two imply that every simple cycle spans all vertices and therefore has the same odd length m. The same no-even-cycle theorem applies. Consecutive pairing still constructs a maximum matching, with (m-1)/2 edges.

**Theorem 1.3 (Every weighted even cycle).**

$$\forall V \in Type,\; [\mathrm{Fintype}\left(V\right)] \forall K \in Type,\; [\mathrm{Field}\left(K\right)] [\mathrm{CharP}\left(K, 2\right)] \forall n \in \mathrm{Nat},\; \forall A \in \mathrm{Matrix}\left(V, V, K\right),\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall e \in \mathrm{GraphIso}\left(\mathrm{evenCycleGraph}\left(n\right), G\right),\; ((\mathrm{IsSymm}\left(A\right)) \land \left(\forall u \in V,\; \forall v \in V,\; (\mathrm{Adj}\left(G, u, v\right)) \Leftrightarrow A\left(u\right)\left(v\right) \ne 0\right)) \Rightarrow \mathrm{rank}\left(A\right) = \mathrm{If}\left(\prod_{i \in \mathrm{Fin}\left(n + 2\right)} A\left(e\left(\operatorname{Sum}.\operatorname{inl}\left(i\right)\right)\right)\left(e\left(\operatorname{Sum}.\operatorname{inr}\left(i\right)\right)\right) = \prod_{i \in \mathrm{Fin}\left(n + 2\right)} A\left(e\left(\operatorname{Sum}.\operatorname{inl}\left(i\right)\right)\right)\left(e\left(\operatorname{Sum}.\operatorname{inr}\left(\mathrm{finRotate}\left(n + 2, i\right)\right)\right)\right), 2 \cdot n + 2, 2 \cdot \left(n + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_even_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual graph isomorphism from evenCycleGraph(n) to the support, take a(i)=A(L(i),R(i)) and b(i)=A(L(i),R(sigma(i))). Exact support makes these nonzero and makes all same-class entries zero. Symmetry identifies the other off-diagonal block with the transpose. Reindexing the actual matrix and applying cyclic_bipartite_rank gives rank 2n+2 when product(a)=product(b), and 2(n+2) otherwise. Thus at length L=2(n+2), the two possibilities are L-2 and L.

**Theorem 1.4 (The Actual Binary Adjacency Matrix).**

$$\forall V \in Type,\; [\mathrm{Fintype}\left(V\right)] \forall n \in \mathrm{Nat},\; \forall G \in \mathrm{SimpleGraph}\left(V\right),\; \forall e \in \mathrm{GraphIso}\left(\mathrm{evenCycleGraph}\left(n\right), G\right),\; (\mathrm{IsGraphIso}\left(e, \mathrm{evenCycleGraph}\left(n\right), G\right)) \Rightarrow \mathrm{rank}\left(\mathrm{adjMatrix}\left(G, \mathrm{ZMod}\left(2\right)\right)\right) = 2 \cdot n + 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_even_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type and every actual graph isomorphism from evenCycleGraph(n) to G, G.adjMatrix(ZMod(2)) has rank 2n+2. Each of its entries on the two actual alternating edge families is one. This directly applies rank_even_cycle, and the stabilizer proof consumes it after proving that the actual same-component mask restriction equals this actual adjacency matrix.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_even_adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_even_cycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_odd_cycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_path`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/NoEvenCycleRank](NoEvenCycleRank.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/WeightedCycleKernel](WeightedCycleKernel.md)
