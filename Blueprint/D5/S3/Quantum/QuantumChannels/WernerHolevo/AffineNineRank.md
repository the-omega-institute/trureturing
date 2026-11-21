# Choi rank and decomposition of the symmetric Werner–Holevo channel

## Abstract

Choi rank and decomposition of the symmetric Werner–Holevo channel.

**Theorem 1.1 (Choi rank of the symmetric channel).**

$$\operatorname{rank}\left(J_{\phi}\right) = \frac{n(n+1)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineRank.choiRank_symmetricWernerHolevo` (`✓ std3`). ∎

*Citation.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

For a finite index type of cardinality n, the unnormalized Choi operator is 2/(n+1) times the projection onto the symmetric subspace of the two tensor factors. Under vectorization its range is the entire space of n by n complex symmetric matrices. The n diagonal coordinates and one coordinate per unordered pair of distinct indices give dimension n(n+1)/2. The Choi matrix of a single unitary conjugation has rank at most one, so every finite mixture needs at least this many terms.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineRank.choiRank_symmetricWernerHolevo`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../../Foundation/FiniteKrausRepresentation.md)
