# Three effects with equal rank caps

## Abstract

Sharp attained spectral entropy for three equally capped effects

**Theorem 1.1 (Exact attained spectral entropy).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/EqualBlockEffects.isGreatest_effectEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/EqualBlockEffects.isGreatest_effectEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Åberg (2006). *Quantifying Superposition*. URL: <https://arxiv.org/abs/quant-ph/0612146>.

*Acknowledgement.* Chi-Kwong Li and Yiu-Tung Poon (2003). *Principal Submatrices of a Hermitian Matrix*. DOI: [10.1080/0308108031000069164](https://doi.org/10.1080/0308108031000069164). URL: <https://doi.org/10.1080/0308108031000069164>.

*Acknowledgement.* Pedro G. Massey (2010). *Non-commutative Schur–Horn theorems and extended majorization for Hermitian matrices*. DOI: [10.1080/03081080802677615](https://doi.org/10.1080/03081080802677615). URL: <https://arxiv.org/abs/0712.2246>.

*Commentary.*

On a complex carrier of dimension d, take three positive semidefinite matrices of trace d/3, rank at most m, and sum equal to identity. Let ℓ = max(d − m, 0) and assume 3ℓ ≤ d. Set b = d − 3ℓ. For either φ(x) = −x log x or φ(x) = −(1 − x) log(1 − x), using the zero-log convention, the maximum of the sum of φ over the three spectra is 3(2ℓ)φ(1/2) + 3bφ(1/3).

In each eigenbasis, the largest min(d, m) eigenvalues carry the effect. The map that stacks all excluded coordinates has rank at most 3ℓ. Project onto a b-dimensional subspace of its kernel. The projection diagonal in each eigenbasis gives weights in [0, 1] of total b, supported on the retained coordinates. Applying the existing weighted spectral inequality to one minus the eigenvalues on these coordinates bounds the sum of the smallest b retained eigenvalues by the corresponding compressed trace. The three compressed traces sum to b. The supporting lines at 1/2 and 1/3 use the top 2ℓ and last b retained coordinates respectively. The affine correction is the derivative difference times the excess of the total tail over b, so it is nonpositive.

For attainment, split the carrier into three ℓ-dimensional coordinate spaces and one b-dimensional space. An effect is zero on its own ℓ-dimensional space, equals one half on each of the other two, and equals one third on the common space. This includes ℓ = 0 and b = 0.

The objective here is the unnormalized matrix spectral sum. The projection formulation requires a separate identification with the original coordinate-record channel and a realization with fixed flat diagonal.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/EqualBlockEffects.isGreatest_effectEntropy`
- Dependency: [D5/S3/Quantum/PureState/PhaseRecordSpectralMemory](../../PureState/PhaseRecordSpectralMemory.md)
