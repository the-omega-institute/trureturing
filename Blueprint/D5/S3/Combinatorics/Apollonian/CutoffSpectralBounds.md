# Actual cutoff spectral bounds

## Abstract

Euclidean spectral remainder bounds for the actual finite inner-face Apollonian graphs.

**Definition 1.1 (The actual directed late matrix).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.lateDirected`

*Formalization.* `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.lateDirected` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all natural k,t, lateDirected k t is a real matrix on the actual LateVertex k t type. Its u,v entry is one exactly when the constructed graph has the edge u→v oriented from strictly younger to strictly older birth, and zero otherwise. The actual late ordinary adjacency is the sum of this matrix and its transpose.

**Theorem 1.2 (The actual late adjacency operator bound).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural k,t, the Euclidean L2 operator norm of lateAdjacency k t is at most 2*sqrt(3*(3*2^(k+t-k-1))). The exponent uses natural subtraction. The outgoing row sums of the directed matrix are at most three, and its incoming column sums are at most 3*2^(k+t-k-1), by the proved constructor-derived orientation and degree laws. The Schur bound controls each direction and transposition preserves the L2 norm. Empty late sets are included. No degree or spectral estimate is assumed.

**Theorem 1.3 (Uniform bound with the original normalization).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_normalized_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_normalized_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural cutoff k and natural t≥1, the L2 operator norm of lateAdjacency k t divided by the real power 2^((k+t)/2) is at most 3*sqrt(2)/2^(k/2). The exponents in both real powers use real division by two. The bound is uniform in the later stage t and includes odd stages. It concerns the late induced block of the actual graph, and does not itself establish the ordered second-eigenvalue limit.

## References

- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.lateDirected`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_norm_le`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_normalized_le`
- Dependency: [D5/S3/Combinatorics/Apollonian/InnerFaceStages](InnerFaceStages.md)
- Dependency: [D5/S3/SpectralTopology/SchurOperatorBound](../../SpectralTopology/SchurOperatorBound.md)
