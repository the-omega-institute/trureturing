# Edge Connectivity and Binary Gradient Decoding

## Abstract

Edge connectivity gives deterministic unique recovery of a binary edge gradient under fewer than half the cut size in arbitrary edge errors.

**Theorem 1.1 (Unique recovery of a noisy binary edge gradient).**

$$\operatorname{IsEdgeConnected}\left(G, k\right) \land 2 \times t < k \land \operatorname{hammingDist}\left(r, \operatorname{edgeDifferential}\left(G, x\right)\right) \leq t \Rightarrow \exists! c, c \in \operatorname{range}\left(\operatorname{edgeDifferential}\left(G\right)\right) \land \operatorname{hammingDist}\left(r, c\right) \leq t$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/EdgeConnectivityDecoding.edge_gradient_unique_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a simple graph with finitely many edges, delta its binary vertex-to-unordered-edge differential, and k and t natural numbers. If G is k-edge-connected and 2t<k, then any received edge labeling within Hamming distance t of delta(x) has exactly one gradient codeword within distance t. The theorem identifies the edge word, not the vertex labels, which retain a constant ambiguity.

For two gradient words at distance less than k, delete precisely their disagreement edges. Their number is the Hamming distance. Edge connectivity supplies a walk after deletion between the endpoints of every original edge. Along each surviving edge, the sum of the two vertex labelings is constant. Walking between the endpoints forces the original edge labels to agree. Finally, the Hamming triangle inequality bounds the distance between two candidates by 2t.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/EdgeConnectivityDecoding.edge_gradient_unique_recovery`
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](SimpleGraphCycleSpace.md)
