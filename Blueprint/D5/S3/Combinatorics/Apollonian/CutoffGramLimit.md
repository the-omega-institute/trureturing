# Fixed-cutoff Gram limit

## Abstract

The actual fixed-cutoff Gram matrices converge to their diagonal face weights.

**Definition 1.1 (The normalized actual Gram matrix).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.normalizedGram`

*Formalization.* `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.normalizedGram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For natural k,t, normalizedGram k t is 2^(-(k+t)) times B B^T on the fixed actual vertex set Vertex k, where B=cutoffBlock k t. Powers here have natural exponents before inversion. The matrix comes from the ordinary zero-one graph adjacency.

**Definition 1.2 (The limiting face-weight diagonal).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.limitingDiagonal`

*Formalization.* `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.limitingDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For natural k, limitingDiagonal k has diagonal entry faceCount k u divided by 2^k at each actual old vertex u, and zero off the diagonal.

**Theorem 1.3 (Convergence on the fixed old vertex set).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.normalized_gram_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.normalized_gram_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For each natural cutoff k, normalizedGram k t tends as t tends to infinity to limitingDiagonal k in the finite matrix topology, hence also for the Euclidean operator norm. The diagonal uses the exact doubling recurrence of incident inner faces and the exact degree increments. Every off-diagonal entry lies between zero and 2t/2^(k+t), which tends to zero. The cutoff is fixed before taking the stage limit. This statement alone does not identify the second ordered eigenvalue of the limiting diagonal.

## References

- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.limitingDiagonal`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.normalizedGram`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffGramLimit.normalized_gram_tendsto`
- Dependency: [D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds](CutoffSpectralBounds.md)
