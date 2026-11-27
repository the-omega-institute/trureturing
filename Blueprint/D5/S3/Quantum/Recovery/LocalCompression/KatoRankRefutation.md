# A faithful classical family for Kato's rank proposal

## Abstract

The exact recovery dimension is n and the unrestricted Choi marginal-rank minimum is one.

Kato's equation (17) defines the normalized Choi state by applying the conditional expectation to the second half of a normalized Bell pair. Equation (61) proposes taking the least marginal rank over joint unitaries on those two factors. Theorem 1 and equation (19) use a purification and its Schmidt rank. Equation (22) gives the rank of the original Choi state, and equation (62) counts posterior classes for a classical law.

**Theorem 1.1 (Exact recovery and Choi marginal rank for every alphabet size).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.faithful_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.faithful_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Acknowledgement.* Ky Fan (1949). *On a Theorem of Weyl Concerning Eigenvalues of Linear Transformations I*. DOI: [10.1073/pnas.35.11.652](https://doi.org/10.1073/pnas.35.11.652). URL: <https://pmc.ncbi.nlm.nih.gov/articles/PMC1063101/>.

*Commentary.*

For every n ≥ 1 and 0 < t < 1, give the pair (a,b) probability (t times the indicator of a = b plus (1−t)/n) divided by n. Every joint weight is positive and both marginals are uniform. Applying a channel on B fixes the bipartite density state exactly when it fixes every conditional state on B given A. Their uniform mixture is the reference state. Different labels have different likelihood vectors, so the exact diagonal recovery theorem gives minimum dimension n over all CPTP encoders and decoders.

The conditional matrices have diagonal commutant since each pair of coordinates is separated by a conditional law. The trace conditional expectation is singleton coordinate pinching. Its normalized Choi state has diagonal weight 1/n at each (b,b) and zero elsewhere. The unitary permutation takes the basis ket (x,y) to (x−y mod n,y). Tracing the second factor after conjugation leaves the rank-one projector onto coordinate zero. Every candidate marginal has trace one, which proves that the least rank is one. The dimensions agree when n = 1.

**Definition 1.2 (The restriction of equation (61) to the faithful family).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.claim`

*Formalization.* `D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Commentary.*

For every member of the family with n ≥ 2, the exact recovery dimensions and the attainable unitary Choi marginal ranks have the same least element.

**Theorem 1.3 (The two minima differ).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kohtaro Kato (2025). *Exact and Local Compression of Quantum Bipartite States*. DOI: [10.1109/TIT.2025.3562884](https://doi.org/10.1109/TIT.2025.3562884). URL: <https://arxiv.org/abs/2309.07434>.

*Commentary.*

With n = 2 and t = 1/2 the four probabilities in basis order are (3,1,1,3)/8. The recovery minimum is two and the marginal-rank minimum is one, contradicting the common-minimum proposal.

Reeb and Wolf use related grouping of joint eigenvalues into product-basis rows in Section 3.3 following Proposition 5. Fan's eigenvalue variational principle bounds the mass that a fixed number of marginal coordinates can capture.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.faithful_family`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.result`
- Dependency: [D5/S3/Quantum/Measurement/Auric/CoordinatePinching](../../Measurement/Auric/CoordinatePinching.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/LiuWildChoiObstruction](../../ProcessReconstruction/LiuWildChoiObstruction.md)
- Dependency: [D5/S3/Quantum/Recovery/DiagonalRecordCapacity](../DiagonalRecordCapacity.md)
