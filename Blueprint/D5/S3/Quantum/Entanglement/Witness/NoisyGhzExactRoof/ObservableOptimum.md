# Noisy GHZ: ObservableOptimum

## Abstract

Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.

Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.

Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.

Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.

The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.

**Theorem 1.1 (The source constant-sector pure optimizer).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.chi_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.chi_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual chi vector has one optimalAlpha amplitude and d-1 optimalBeta amplitudes. Its norm is one, its P and G means are one and F, and its all-cut pure measure equals the complete optimum, including F=1/d and F=1.

**Theorem 1.2 (The measured means W,Q).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.observable_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.observable_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every density state, y=1-q and f=(1-q)/d-w. Thus the two G,P means encode exactly the two W,Q measurements.

**Theorem 1.3 (Attained all-state two-mean minimum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.two_mean_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.two_mean_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Every feasible pair has an actual density operator and the explicit three-component normalized ensemble twoMeanWeights/twoMeanStates. Their matrix sum, both means, average entanglement and exact roof are proved. The zero branch uses computational products, including qWord=|0,1,2,0,...>; the positive branch mixes chi with qWord. This optimizer is not asserted to be the noisy matrix.

**Theorem 1.4 (The complete original single-witness optimum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.witness_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.witness_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

On the full interval -(d-1)/d through 1/d, epsilonWitness equals twoMeanOptimum d (1/d-w) 1. epsilonWitness uses the original hatE two-vector supremum, and epsilonO is its exact specialization at witnessValue. The proof covers both spectral endpoints and the nonnegative-w zero interval using actual finite optimizers and finite supporting slopes.

**Theorem 1.5 (constantVector apply).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.constantVector_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.constantVector_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.6 (constantVector off).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.constantVector_off`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.constantVector_off` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.7 (optimal amplitudes).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.optimal_amplitudes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.optimal_amplitudes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.8 (epsilonO bridge).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.epsilonO_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.epsilonO_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.9 (qWord outside).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.qWord_outside`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.qWord_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.10 (twoMean scaling).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.twoMean_scaling`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.twoMean_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.chi_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.constantVector_apply`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.constantVector_off`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.epsilonO_bridge`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.observable_correspondence`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.optimal_amplitudes`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.qWord_outside`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.twoMean_scaling`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.two_mean_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.witness_optimum`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/Foundations](Foundations.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/TwoMeanBound](TwoMeanBound.md)
