# Connected forcing polynomial of the spider

## Abstract

For k ≥ 3 arms of lengths h_j ≥ 1 the spider S(h_1, …, h_k) has connected forcing polynomial x^k (x ∏_j F_{h_j} + Σ_j ∏_{t≠j} F_{h_t}), where F_h = 1 + x + ⋯ + x^{h−1}.

**Definition 1.1 (The spider).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.spider`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.spider` (`✓ std3`).

*Citation.* Boris Brimkov (2017). *Graph Coloring, Zero Forcing, and Related Problems*. URL: <https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content>.

*Commentary.*

The spider S(h_1, …, h_k) has a centre and k pendant paths, the arms, the jth with h_j vertices. Its vertices are the centre and the pairs (j, p) with p < h_j, the vertex of arm j at distance p + 1 from the centre; the centre is adjacent to each (j, 0) and (j, p) is adjacent to (j, p + 1).

**Definition 1.2 (Centre and initial arm segments).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.body`

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.body` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a tuple ℓ of natural numbers, body ℓ is the set made of the centre and the first ℓ_j vertices of each arm j.

**Theorem 1.3 (Connected forcing sets of the spider).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.connected_forcing_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.connected_forcing_iff` (`✓ std3`). ∎

*Citation.* Boris Brimkov (2017). *Graph Coloring, Zero Forcing, and Related Problems*. URL: <https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content>.

*Commentary.*

For k ≥ 3 arms of positive lengths, a vertex set induces a connected subgraph and is a zero forcing set exactly when it is body ℓ for a tuple with ℓ_j ≤ h_j for every arm and ℓ_j = 0 for at most one arm.

A walk leaving a region of the graph passes through the only vertex joining the region to the rest. Hence a connected set without the centre lies in one arm, and a connected set containing the centre meets each arm in an initial segment. A set inside one arm forces nothing beyond that arm and the centre, because the centre then has two white neighbours in other arms. If two arms are untouched, the centre always keeps two white neighbours there. With at most one untouched arm, every touched arm forces outward along itself and the centre then forces the remaining arm. This is the characterization in the proof of Proposition 7.11 of B. Brimkov, Graph Coloring, Zero Forcing, and Related Problems (PhD thesis, Rice University, 2017).

**Theorem 1.4 (The polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.result` (`✓ std3`). ∎

*Citation.* Boris Brimkov (2017). *Graph Coloring, Zero Forcing, and Related Problems*. URL: <https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content>.

*Commentary.*

For k ≥ 3 arms of lengths h_j ≥ 1, the number of connected forcing sets of the spider of size i is the coefficient of x^i in x^k (x ∏_j F_{h_j} + Σ_j ∏_{t≠j} F_{h_t}), with F_h = Σ_{e<h} x^e.

The set body ℓ has 1 + Σ_j ℓ_j vertices, and distinct tuples give distinct sets. Summing x^{1+Σℓ_j} over the tuples touching every arm gives x ∏_j (x + ⋯ + x^{h_j}) = x^{k+1} ∏_j F_{h_j}; over the tuples leaving exactly arm j untouched it gives x ∏_{t≠j} (x F_{h_t}) = x^k ∏_{t≠j} F_{h_t}. This is Proposition 7.11 of Brimkov (2017), whose coefficient of x^j counts the compositions s(j − 1; h_1, …, h_k) and s(j − 1; h_1, …, h_{ℓ−1}, h_{ℓ+1}, …, h_k). The hypotheses are needed: with two arms the spider is a path, whose end vertices are connected forcing sets of size 1 while the formula has no x term; with exactly one arm j of length 0 the graph is the spider on the other arms, while the formula becomes x^k ∏_{t≠j} F_{h_t}, which counts only the sets touching every other arm.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.body`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.connected_forcing_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.spider`
- Dependency: [D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation](ConnectedForcingCrossingRefutation.md)
