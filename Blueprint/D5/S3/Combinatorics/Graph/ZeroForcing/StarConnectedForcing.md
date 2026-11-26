# Connected forcing polynomial of the star

## Abstract

The connected forcing polynomial of the star K_{1,n−1} is (n − 1)x^{n−1} + x^n for n ≥ 4 and equals that of the path P_n for n ≤ 3.

**Definition 1.1 (The star).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.starGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.starGraph` (`✓ std3`).

*Citation.* Boris Brimkov (2017). *Graph Coloring, Zero Forcing, and Related Problems*. URL: <https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content>.

*Commentary.*

The star K_{1,n−1} on the vertices 0, …, n − 1 with centre 0: two distinct vertices are adjacent exactly when one of them is the centre.

**Theorem 1.2 (Connected forcing sets of the star).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.connected_forcing_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.connected_forcing_iff` (`✓ std3`). ∎

*Citation.* Boris Brimkov (2017). *Graph Coloring, Zero Forcing, and Related Problems*. URL: <https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content>.

*Commentary.*

For n ≥ 1 a vertex set S of K_{1,n−1} induces a connected subgraph and is a zero forcing set exactly when either S contains the centre and misses at most one leaf, or n ≤ 3 and S is a single leaf.

Every set containing the centre is connected, and without the centre a connected set is a single leaf. If two leaves are white, every black leaf has only the centre as neighbour and the centre has two white neighbours, so nothing outside S and the centre ever turns black. The centre with at most one white leaf forces that leaf. A single leaf forces the centre, which then forces the last leaf when there are at most two leaves. This is the unit-arm case of the counting in Proposition 7.11 of B. Brimkov, Graph Coloring, Zero Forcing, and Related Problems (PhD thesis, Rice University, 2017).

**Theorem 1.3 (The coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.result` (`✓ std3`). ∎

*Citation.* Boris Brimkov (2017). *Graph Coloring, Zero Forcing, and Related Problems*. URL: <https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content>.

*Commentary.*

For n ≥ 1 the number of connected forcing sets of K_{1,n−1} of size i is [i = n] + (n − 1)[i = n − 1] + (n − 1)[i = 1 and n ≤ 3]. For n ≥ 4 this gives Z_c(K_{1,n−1}; x) = (n − 1)x^{n−1} + x^n, and for every n ≤ 3 the coefficients agree with those of the path P_n, the two smaller nontrivial stars K_{1,1} = P_2 and K_{1,2} ≅ P_3 having the path formulas.

The whole vertex set counts once, the n − 1 sets missing one leaf count at size n − 1, and the n − 1 single leaves count at size 1 when n ≤ 3. The general formula needs n ≥ 1: on the empty vertex set no set is connected, while the formula gives 1 at i = 0; the comparison with the path holds for every n ≤ 3, the empty graph included. The case n ≥ 4 is Proposition 7.11 of Brimkov (2017) with every pendant path of one vertex.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.connected_forcing_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.starGraph`
- Dependency: [D5/S3/Combinatorics/Graph/ZeroForcing/PathConnectedForcing](PathConnectedForcing.md)
