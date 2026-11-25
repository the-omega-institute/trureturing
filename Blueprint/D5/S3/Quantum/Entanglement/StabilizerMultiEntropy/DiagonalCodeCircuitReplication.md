# Actual diagonal circuit coverage and coordinate replication

## Abstract

An exact coverage threshold for diagonal finite-field circuits with arbitrary positive copy counts.

**Theorem 1.1 (The largest copy count controls an even circuit).**

$$\forall C \in \operatorname{EvenFiniteFieldColumnCircuitsAtLeastFour}\left(\right),\; \forall J \in \operatorname{PositiveCopyProfiles}\left(C\right),\; \forall K \in \operatorname{RealsAboveOne}\left(\right),\; \operatorname{HitLaw}\left(\operatorname{ActualCopiedCircuitMoments}\left(C, J, K\right)\right) \Leftrightarrow \operatorname{Le}\left(\operatorname{Pow}\left(\operatorname{Pow}\left(\operatorname{FieldCardinality}\left(C\right), \operatorname{Sub}\left(1, K\right)\right), \operatorname{Sub}\left(\operatorname{CircuitSize}\left(C\right), 1\right)\right), \operatorname{Mul}\left(\operatorname{Pow}\left(\operatorname{Sub}\left(1, \operatorname{Pow}\left(\operatorname{FieldCardinality}\left(C\right), \operatorname{Sub}\left(1, K\right)\right)\right), \operatorname{Sub}\left(\operatorname{CircuitSize}\left(C\right), 2\right)\right), \operatorname{Add}\left(\operatorname{Pow}\left(\operatorname{FieldCardinality}\left(C\right), \operatorname{Sub}\left(1, K\right)\right), \operatorname{Inv}\left(\operatorname{Sub}\left(\operatorname{Pow}\left(2, \operatorname{MaxCopyCount}\left(J\right)\right), 1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalCodeCircuitReplication.physical_even_fiber_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

A column circuit is a linearly dependent family whose every proper subfamily is independent. The actual diagonal density is the uniform mixture of evaluations of linear functionals. A diagonal marginal is indexed by a physical subset of tagged copies, while its rank is the rank of the underlying occupied columns. No physical independence of copies is assumed.

For each original column, sum the signed weights of all nonempty subsets of its copies. This is minus one if the label has any marked copy in that class, and the copy-subset count minus one otherwise. The independent product and the single full-circuit correction are the two surviving terms. Positive rescaling removes the unoccupied fiber factors.

For even circuit size and nonempty fibers, the worst odd support marks every class except one with the largest copy count. Thus only that maximum enters the exact threshold. For odd unreplicated size at least three the threshold is exactly x at most one half. Omitting a coordinate is not covered by the even theorem's nonempty-fiber hypotheses; the general signed formula still applies.

**Theorem 1.2 (Actual doubled four-bit circuit coefficient).**

$$\forall K \in \operatorname{PositiveReals}\left(\right),\; \operatorname{ActualDoubledFourWalshMass}\left(K\right) = \operatorname{Div}\left(\operatorname{Sub}\left(\operatorname{Mul}\left(\operatorname{Pow}\left(\operatorname{Sub}\left(1, \operatorname{Pow}\left(2, \operatorname{Sub}\left(1, K\right)\right)\right), 3\right), \operatorname{Add}\left(1, \operatorname{Mul}\left(3, \operatorname{Pow}\left(2, \operatorname{Sub}\left(1, K\right)\right)\right)\right)\right), \operatorname{Mul}\left(3, \operatorname{Pow}\left(\operatorname{Pow}\left(2, \operatorname{Sub}\left(1, K\right)\right), 3\right), \operatorname{Sub}\left(1, \operatorname{Pow}\left(2, \operatorname{Sub}\left(1, K\right)\right)\right)\right)\right), 256\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalCodeCircuitReplication.physical_four_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

Use the three standard binary columns and their sum. Duplicate each site, then mark one copy in each of three original classes. The registered observation is the signed Walsh coefficient of the actual eight-site reduced-state trace moments. At x equal to three fifths the original four-site state admits a common classical law while this doubled bin is exactly minus one over 3200.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalCodeCircuitReplication.physical_even_fiber_threshold`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalCodeCircuitReplication.physical_four_readout`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeCoverage](DiagonalLinearCodeCoverage.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments](DiagonalLinearCodeMoments.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh](GraphStateSmallOrderWalsh.md)
