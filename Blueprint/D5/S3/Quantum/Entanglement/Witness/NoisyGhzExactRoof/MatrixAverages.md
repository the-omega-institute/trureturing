# Noisy GHZ: MatrixAverages

## Abstract

Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.

Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.

Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.

Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.

The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.

**Theorem 1.1 (The complete truncated radical).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.twoMeanOptimum_max`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.twoMeanOptimum_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

On the closed triangle zero at most f at most y, the piecewise optimum equals the squared positive part of sqrt((d-1)f)-sqrt(y-f), divided by d.

**Theorem 1.2 (The actual disjoint support-matrix decomposition).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.support_projector_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.support_projector_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The original complex matrix P equals the constant-word projector C plus the sum of the off-constant projectors for all anchored bipartitions. This is a full matrix equality, not only a dimension count.

**Theorem 1.3 (The full finite basis-average matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.basis_average_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.basis_average_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The d actual chi projectors average to F*G+(1-F)/(d-1)*(C-G), with exact arbitrary-d coefficients and endpoint domains.

**Theorem 1.4 (The full finite phase-average matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.phase_average_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.phase_average_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For each nonempty proper cut, the 3^d actual cutState projectors average to F*G+(1-F)/(d*(d-1))*T_A. All unwanted matrix entries cancel by independent-coordinate character orthogonality, for arbitrary d.

**Theorem 1.5 (noisyDensity matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.noisyDensity_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.noisyDensity_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.6 (diagonal projector sum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.diagonal_projector_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.diagonal_projector_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.basis_average_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.diagonal_projector_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.noisyDensity_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.phase_average_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.support_projector_decomposition`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.twoMeanOptimum_max`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates](CutStates.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/Foundations](Foundations.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum](ObservableOptimum.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/TwoMeanBound](TwoMeanBound.md)
