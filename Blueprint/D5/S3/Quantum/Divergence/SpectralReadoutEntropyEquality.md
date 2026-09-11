# Spectral Readout Entropy Equality

## Abstract

A unitary readout keeps the Shannon entropy of a spectrum only in the diagonal case.

Matrices are complex and indexed by an arbitrary finite nonempty type n. U is unitary and x is a nonnegative real vector, read as a spectrum. diagonal(x) is the matrix carrying x on its diagonal, and conjugate(U, D) is U times D times the conjugate transpose of U. diagonalPart takes the real parts of the diagonal entries, which is the vector an observer reads off in the basis fixed by U. shannonEntropy is the natural-logarithm entropy of a nonnegative vector, with no normalization assumed.

**Theorem 1.1 (Readout entropy equals spectral entropy exactly in the diagonal case).**

$$\forall n \in FiniteNonemptyType, U \in \operatorname{UnitaryGroup}\left(n\right), x \in \operatorname{NonnegativeVector}\left(n\right),\; \operatorname{shannonEntropy}\left(\operatorname{diagonalPart}\left(\operatorname{conjugate}\left(U, \operatorname{diagonal}\left(x\right)\right)\right)\right) = \operatorname{shannonEntropy}\left(x\right) \Leftrightarrow \operatorname{IsDiag}\left(\operatorname{conjugate}\left(U, \operatorname{diagonal}\left(x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/SpectralReadoutEntropyEquality.spectral_readout_entropy_eq_iff_isDiag` (`✓ std3`). ∎

*Citation.* T. Baumgratz, M. Cramer, M. B. Plenio (2014). *Quantifying Coherence*. URL: <https://arxiv.org/abs/1311.0275v3>.

*Commentary.*

The readout vector is the doubly stochastic image of the spectrum under the matrix of squared moduli of U, so its entropy is at least the spectral entropy. Equality forces all spectral values in each row's nonzero support to coincide with that row's readout value. Thus U diagonal(x) equals diagonal(readout) U, and multiplication by U* proves diagonality. The converse direction is immediate because a diagonal conjugate reproduces the spectrum up to a permutation, and entropy does not see the order of its argument. No normalization, positive definiteness, or distinctness of the spectrum is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/SpectralReadoutEntropyEquality.spectral_readout_entropy_eq_iff_isDiag`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../Entropy/MaxEntropy.md)
