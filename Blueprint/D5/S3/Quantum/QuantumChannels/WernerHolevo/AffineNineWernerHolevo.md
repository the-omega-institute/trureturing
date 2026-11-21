# Symmetric Werner–Holevo rank from affine lines

## Abstract

The symmetric Werner–Holevo channel attains its Choi rank in each dimension 9 to a power at least two.

**Theorem 1.1 (Minimal rank in powers of nine).**

$$\begin{aligned}n&=9^{d},\quad d\in\mathbb{N},\quad d\geq2\\\phi^{+}(X)&=\frac{\operatorname{tr}\left(X\right)I+X^{T}}{n+1},\quad\forall X \in M_{n}(\mathbb{C})\\\operatorname{murank}\left(\phi^{+}\right)&=\frac{n(n+1)}{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo.mixedUnitaryRank_power_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

For every natural exponent d at least two, there exists a completely positive trace-preserving map of type `D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel` on n by n matrices with the displayed action on every complex matrix. Its mixed-unitary rank is the least length of a finite decomposition into unitary conjugations with nonnegative real weights summing to one. The least length is 3321 in dimension 81.

Each direction partitions the affine space into lines of size nine. A flat hollow symmetric unitary acts on each line. The nine-block edge labeling extends to the larger parallel classes. Additive characters turn the distinct endpoint sums into an orthogonal hollow family in each direction. Together with the diagonal characters these matrices form a Hilbert–Schmidt orthogonal basis of the entire complex symmetric matrix subspace.

The basis gives a uniform unitary-conjugation mixture with weights 2/(n(n+1)). The Choi range under vectorization is the entire complex symmetric matrix subspace, of dimension n(n+1)/2. A unitary conjugation has a rank-one Choi matrix, so no shorter finite decomposition can have this range. The all-dimension conjecture remains open.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo.mixedUnitaryRank_power_nine`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasisConcrete](AffineNineBasisConcrete.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineRank](AffineNineRank.md)
