# An integer order barrier in classical binary linear codes

## Abstract

The universal integer-order coverage threshold needs no entanglement.

**Theorem 1.1 (Universal actual coverage iff integer order).**

$$\forall K \in \operatorname{RealsAboveOne}\left(\right),\; \left(\forall C \in \operatorname{FiniteBinaryColumnConfigurations}\left(\right),\; \operatorname{HitLaw}\left(\operatorname{ActualMomentTable}\left(C, K\right)\right)\right) \Leftrightarrow \left(\exists n \in \mathbb{N},\; K = \operatorname{Add}\left(n, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeCoverage.binary_classical_coverage_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

The state is the uniform diagonal density of a binary linear code. A single nonnegative normalized law on subsets must reproduce the physical GCE hit probabilities of every subsystem. At integer order K, draw K−1 independent uniform linear functionals. They all vanish on a selected subsystem with probability equal to its actual trace moment. Uniform thinning gives the hit law.

A projective code has one site for each nonzero binary vector. Its full-label Walsh mass is the normalized product of the projective factors. For any noninteger order there is a code for which exactly the last factor is negative. On 1<K<2 this needs only three sites; in the next band a seven-site Fano code gives an exact mass −1/1728 at q=3. The classification is universal, not a claim that all individual codes fail at noninteger K. The noninteger construction here is binary.

**Theorem 1.2 (Actual seven-site Fano full-label mass).**

$$\forall K \in \operatorname{PositiveReals}\left(\right),\; \operatorname{FullFanoWalshMass}\left(K\right) = \operatorname{Div}\left(\operatorname{Product}\left(\operatorname{FanoFactors}\left(\operatorname{Pow}\left(2, \operatorname{Sub}\left(K, 1\right)\right)\right), 3\right), 128\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeCoverage.physical_fano_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

The registered observable is the signed full-label bin of the actual complex reduced-state trace table, not the characteristic polynomial substituted by assumption. The positive normalization is 2 to the seventh power.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeCoverage.binary_classical_coverage_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeCoverage.physical_fano_readout`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/BinaryProjectiveRankPolynomial](BinaryProjectiveRankPolynomial.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments](DiagonalLinearCodeMoments.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh](GraphStateSmallOrderWalsh.md)
