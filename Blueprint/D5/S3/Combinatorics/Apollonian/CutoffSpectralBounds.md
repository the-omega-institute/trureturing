# Actual cutoff spectral bounds

## Abstract

Euclidean spectral remainder bounds for the actual finite inner-face Apollonian graphs.

**Theorem 1.1 (Row and column bounds control the Euclidean operator).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.l2_opNorm_le_schur`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.l2_opNorm_le_schur` (`✓ std3`). ∎

*Citation.* Jue Xu and LeanPool contributors (2026). *Finite rectangular Schur operator bound*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/LowWeightPauliDynamics/SchurCore.lean>.

*Commentary.*

For every RCLike field K, finite row type I and finite column type J, with decidable equality on J, let A be an I by J matrix over K. If real R,C are nonnegative, every sum over j in J of the norm of A(i,j) is at most R, and every sum over i in I is at most C, then the Euclidean operator norm of A is at most sqrt(R*C). Empty row or column types are included. The norm is explicitly Matrix.Norms.L2Operator. Weighted Cauchy–Schwarz first bounds the squared action of each row, and summation uses the column bounds. The theorem is a minimal licensed port of Jue Xu's proof and is consumed by the actual Apollonian late adjacency estimate.

**Definition 1.2 (The actual directed late matrix).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.lateDirected`

*Formalization.* `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.lateDirected` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For all natural k,t, lateDirected k t is a real matrix on the actual LateVertex k t type. Its u,v entry is one exactly when the constructed graph has the edge u→v oriented from strictly younger to strictly older birth, and zero otherwise. The actual late ordinary adjacency is the sum of this matrix and its transpose.

**Theorem 1.3 (The actual late adjacency operator bound).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural k,t, the Euclidean L2 operator norm of lateAdjacency k t is at most 2*sqrt(3*(3*2^(k+t-k-1))). The exponent uses natural subtraction. The outgoing row sums of the directed matrix are at most three, and its incoming column sums are at most 3*2^(k+t-k-1), by the proved constructor-derived orientation and degree laws. The Schur bound controls each direction and transposition preserves the L2 norm. Empty late sets are included. No degree or spectral estimate is assumed.

**Theorem 1.4 (Uniform bound with the original normalization).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_normalized_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_normalized_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural cutoff k and natural t≥1, the L2 operator norm of lateAdjacency k t divided by the real power 2^((k+t)/2) is at most 3*sqrt(2)/2^(k/2). The exponents in both real powers use real division by two. The bound is uniform in the later stage t and includes odd stages. It concerns the late induced block of the actual graph, and does not itself establish the ordered second-eigenvalue limit.

## References

- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.l2_opNorm_le_schur`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.lateDirected`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_norm_le`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.late_adjacency_normalized_le`
- Dependency: [D5/S3/Combinatorics/Apollonian/InnerFaceStages](InnerFaceStages.md)
