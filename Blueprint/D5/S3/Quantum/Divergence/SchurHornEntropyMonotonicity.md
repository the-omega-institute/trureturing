# Schur--Horn Shannon Entropy Monotonicity

## Abstract

A unitary spectral readout cannot decrease finite Shannon entropy.

**Theorem 1.1 (Unitary spectral readout cannot decrease Shannon entropy).**

$$
\operatorname{shannonEntropy}(x) \leq
\operatorname{shannonEntropy}\left(\operatorname{diagonalPart}\left(U\operatorname{diagonal}(x)U^*\right)\right)
$$

*Formalization.* `D5/S3/Quantum/Divergence/SchurHornEntropyMonotonicity.spectral_readout_entropy_le` (validation pending).

*Source.* Repository-derived.

*Commentary.*

For a finite index type n, a unitary matrix U, and a nonnegative real spectrum x, form U diagonal(x) U* and read the real parts of its diagonal entries. The readout vector is the squared-entry-norm matrix of U applied to x.

The squared-entry-norm matrix is doubly stochastic. Row-wise Jensen for the convex function t log t, followed by the column-sum identity, shows that the readout's x log x sum is no larger than the spectral sum. Negating gives the Shannon entropy inequality.

This is the finite Schur--Horn bridge used by the later pinching and Klein targets. No normalization, strict positivity, or distinct eigenvalue assumption is required.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/SchurHornEntropyMonotonicity.spectral_readout_entropy_le`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../Entropy/MaxEntropy.md)
- Dependency: [D5/S3/Weil/ZetaLinear/VonNeumann](../../Weil/ZetaLinear/VonNeumann.md)
