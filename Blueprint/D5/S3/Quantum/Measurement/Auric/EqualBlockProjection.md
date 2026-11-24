# Flat-rank states and equal coordinate blocks

## Abstract

Sharp attained entropy gain of a flat-rank state under three equal coordinate blocks

**Theorem 1.1 (Exact attained coordinate pinching gain).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/EqualBlockProjection.isGreatest_flat_record_gain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/EqualBlockProjection.isGreatest_flat_record_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Åberg (2006). *Quantifying Superposition*. URL: <https://arxiv.org/abs/quant-ph/0612146>.

*Acknowledgement.* Chi-Kwong Li and Yiu-Tung Poon (2003). *Principal Submatrices of a Hermitian Matrix*. DOI: [10.1080/0308108031000069164](https://doi.org/10.1080/0308108031000069164). URL: <https://doi.org/10.1080/0308108031000069164>.

*Acknowledgement.* Pedro G. Massey (2010). *Non-commutative Schur–Horn theorems and extended majorization for Hermitian matrices*. DOI: [10.1080/03081080802677615](https://doi.org/10.1080/03081080802677615). URL: <https://arxiv.org/abs/0712.2246>.

*Commentary.*

Fix three coordinate fibers each of size m > 0. Optimize the von Neumann entropy gain of their coordinate pinching channel over P/r, where P is a Hermitian projection of rank 1 ≤ r ≤ 3m and every diagonal entry is r/(3m).

Let d = min(r, 3m − r), ℓ = max(d − m, 0), and b = d − 3ℓ. When 2r ≤ 3m the attained gain is (3ℓ log 2 + b log 3)/r. When 2r > 3m it is (3ℓ log 2 + 2b log(3/2))/r. In particular the gain is zero at full rank.

Use an isometric frame for P in the first case and for its complement in the second case. Its coordinate row blocks have positive Gram effects summing to identity, each with trace d/3 and rank at most m. The pinched matrix is the direct sum of the row products or their complements. Rectangular Gram products have the same nonzero eigenvalues with multiplicity. The two scalar objectives vanish at zero, and trace preservation cancels the logarithm of the normalization, yielding the spectral objective divided by the original rank r.

To realize the maximum, factor each attaining effect through m rows, assign its nonzero eigenvectors to distinct Fourier columns, and use the normalized Fourier rows to make every diagonal entry of the row product equal to its trace divided by m. Stack the resulting rows in the given fibers. Their Grams sum to identity, so the stack gives the required projection or complementary projection with the prescribed diagonal.

Åberg supplies the entropy-gain interpretation, with the projective embedding extension due to Bischof, Kampermann and Bruß. Li and Poon and Massey give the broader spectral feasibility context. The equal-block maximum follows from the rank-capped effect theorem and the explicit Fourier realization.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/EqualBlockProjection.isGreatest_flat_record_gain`
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](../../Divergence/VonNeumannEntropyPinching.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/CoordinatePinching](CoordinatePinching.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/EqualBlockEffects](EqualBlockEffects.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/ProjectionFrames](ProjectionFrames.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../../QuantumChannels/TomiyamaDiagonalKPositivity.md)
