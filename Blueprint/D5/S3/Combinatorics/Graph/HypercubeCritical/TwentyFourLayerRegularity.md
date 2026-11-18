# Twenty Four Layer Regularity

## Abstract

Twenty Four Layer Regularity

Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f2(Q9) is three or four. This abstract graph result proves a conditional regularity step and does not resolve that external problem. It has no cube embedding premise.

The structural hypothesis D is global: for every root x and distinct vertices y,z at actual extended graph distance four from x, if y,z both have full graph degree three and every actual neighbor of each has distance three from x, their full neighborFinset neighborhoods are disjoint. D is a neighborhood disjointness hypothesis, not an assumed layer count or assumed regularity conclusion. Deriving D from an induced cube embedding is a separate obligation.

The graph is finite and simple, with bipartition sides L,R of size twelve, every vertex of full degree two or three, exactly four degree-two vertices on each side, independent degree-two vertices, and extended girth at least eight. Positive degree makes the bipartition cover every vertex. Under D, every full-degree-three vertex has exactly two full-degree-three neighbors.

For a high root x with three high neighbors, its actual first layer has size three and its actual second layer size six. Girth gives unique short paths and disjoint forward branches. If b is the number of lows in the second layer, the third layer has size twelve minus b, so b is three or four. The five remaining same-side vertices have no neighbor in the first layer. When b is three, four of them are high and D would place twelve distinct neighbors in a third layer of size nine. Consequently every high root with three high neighbors sees all four same-side lows at distance two.

When b is four, the third layer has size eight, all five remaining same-side vertices are high, and exactly one opposite-side vertex q is outside the first and third layers. All neighbors of q lie among those five vertices. If q were low, the other three high vertices would require nine distinct neighbors in a third layer of size eight by D. Thus q is high, and there are two high vertices T outside its three neighbors. Applying the preceding all-lows-at-distance-two result at q makes every opposite-side low adjacent to a neighbor of q. Such a low already has its unique second-layer parent relative to x, exhausting its full degree two. It cannot meet T. D therefore forces the six distinct neighbors of T into the four high vertices of the third layer, a contradiction.

Thus a high vertex never has three high neighbors. The existing weighted incidence identity gives total high-neighbor degree sixteen on each side, each of which has eight high vertices. The upper bound two and equality of sums force every one of these degrees to equal two. All helper declarations are private; only claim and its literal negation result are public.

**Definition 1.1 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exist n, a simple graph G on Fin n, bipartition sides L,R of size twelve, degrees two or three, four independent degree-two vertices on each side, girth at least eight, and the global distance-layer neighborhood disjointness property D, together with a full-degree-three vertex whose number of full-degree-three neighbors is different from two.

**Theorem 1.2 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem has literally type Not claim. It refutes a failure of high-neighbor regularity under all the stated graph assumptions and global D. It neither proves D for cube subgraphs nor settles f2(Q9).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting](GirthSliceCounting.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph](SymmetricHighGraph.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoLocal](SymmetricTwentyTwoLocal.md)
