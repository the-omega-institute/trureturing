# Actual cutoff dilation spectrum

## Abstract

Ordered spectra of the actual old-to-late graph block.

**Definition 1.1 (The actual cutoff dilation).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoffDilation`

*Formalization.* `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoffDilation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For natural k,t, the real matrix cutoffDilation k t acts on Vertex k plus LateVertex k t and has blocks [[0,B],[transpose B,0]], where B is the actual zero-one cutoff adjacency block. The two diagonal blocks are zero and the vertex types may have unequal cardinalities.

**Definition 1.2 (The second decreasing dilation eigenvalue).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoffSecond`

*Formalization.* `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoffSecond` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For natural k,t, cutoffSecond k t is index one in the decreasing real Hermitian spectrum of cutoffDilation k t, with algebraic multiplicity. The four persistent seed vertices ensure this index exists.

**Theorem 1.3 (The actual positive second-spectrum bridge).**

Lean statement: `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoff_second_eq_sqrt_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoff_second_eq_sqrt_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rad Sarar Anando (2026). *Second adjacency eigenvalue of Apollonian networks: is theta_2(G_m)/2^(m/2) -> sqrt(2)?*. URL: <https://mathoverflow.net/questions/516405>.

*Commentary.*

For every natural k,t, if the second decreasing eigenvalue of the actual Gram matrix B B^T on Vertex k is strictly positive, then cutoffSecond k t is its positive square root. No equality of the old and late block sizes is assumed. Characteristic-polynomial zero padding and real-to-complex embedding retain the ordered positive prefix, signs and algebraic multiplicities. The positivity premise remains explicit; this conditional identity does not establish the original all-stage adjacency limit.

## References

- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoffDilation`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoffSecond`
- Truth anchor: `D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum.cutoff_second_eq_sqrt_gram`
- Dependency: [D5/S3/Combinatorics/Apollonian/InnerFaceStages](InnerFaceStages.md)
- Dependency: [D5/S3/SpectralTopology/RectangularDilation](../../SpectralTopology/RectangularDilation.md)
