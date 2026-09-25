# Edge Connectivity and Binary Gradient Weight

## Abstract

Edge connectivity is characterized by the weight of every nonconstant binary edge gradient.

**Theorem 1.1 (Edge connectivity from binary gradients).**

$$\operatorname{IsEdgeConnected}(G, k) \iff \forall x, {\exists u, v, \operatorname{x}(u) \neq \operatorname{x}(v)} \Rightarrow k \leq \operatorname{hammingNorm}(\operatorname{edgeDifferential}(G, x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be any simple graph with finitely many edges, k any natural number, and delta the binary vertex-to-edge differential. G is k-edge-connected exactly when every vertex labeling that differs at two vertices has edge word delta(x) of Hamming weight at least k. No connectedness or finiteness assumption on vertices is required. The statement concerns edge words, not uniqueness of vertex labels.

For the forward direction, delete the edges supporting a gradient of weight less than k. A surviving walk between vertices with different labels would force those labels to agree. Conversely, if deleting fewer than k edges separates u from v, label each vertex by membership in the component reachable from u after deletion. This nonconstant labeling has zero gradient on every surviving edge, so its gradient support is contained in the deletion set and has weight less than k.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight`
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](SimpleGraphCycleSpace.md)
