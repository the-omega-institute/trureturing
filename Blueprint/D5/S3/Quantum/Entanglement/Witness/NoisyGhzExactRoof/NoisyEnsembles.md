# Noisy GHZ: NoisyEnsembles

## Abstract

Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.

Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.

Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.

Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.

The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.

**Theorem 1.1 (Exact noisy-matrix means).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_means`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_means` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual complex-matrix real traces are f=1-p+p/M and y=1-p+p*R/M.

**Theorem 1.2 (The affine noisy witness).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.witness_value_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.witness_value_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The original witnessValue is exactly -(d-1)/d+k*p, with the defined source slope.

**Theorem 1.3 (The original noisy single-witness optimum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_witness_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_witness_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every physical p the original epsilonO equals the full feasible-interval optimum at the actual witness trace. It is bridged through the defining hatE, without the disputed all-real-slope antecedent formula.

**Theorem 1.4 (Strict two-observable advantage).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.two_mean_strict_witness_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.two_mean_strict_witness_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

On the full means triangle, y<1 and negative witness imply strict improvement over the complete original single-witness conjugate. The proof compares radicals with their sign conditions and uses no singular endpoint metric.

**Theorem 1.5 (The complete supported source average).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.source_average_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.source_average_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The finite combination S_F of J_F and all anchored H_A,F equals F*G+(1-F)/(R-1)*(P-G), as a full matrix identity.

**Theorem 1.6 (The complete low-noise matrix reconstruction).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.low_noise_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.low_noise_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For 0<=p<=p_W, lowNoiseWeights and lowNoiseStates reconstruct every entry of rho(p). Their index consists of d basis vectors, K*3^d cut-phase vectors, and the actual computational Q sector.

**Theorem 1.7 (An actual attaining low-noise ensemble).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.low_noise_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.low_noise_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The displayed weights are nonnegative and sum to one, every constituent is unit, their projectors reconstruct the actual noisy matrix, and their mean pure measure equals the two-mean value and the actual finite convex roof. The p=0 and p=p_W endpoints are included.

**Theorem 1.8 (Actual cut products at the threshold).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.threshold_constituents_biseparable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.threshold_constituents_biseparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

At p_W the optimal amplitudes are alpha=1 and beta=0. Every constituent genuinely factorizes across its displayed nonempty proper cut or is a computational product; zero roof is not used to infer factorization.

**Theorem 1.9 (Full high-noise matrix reconstruction).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.high_noise_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.high_noise_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For p_W<=p<=1 the explicit finite highNoiseWeights and highNoiseStates mix the threshold ensemble with the computational I/M ensemble, with lambda=(1-p)/(1-p_W).

**Theorem 1.10 (A finite biseparable high-noise ensemble).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.high_noise_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.high_noise_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

All high-noise weights are nonnegative and normalized, all actual constituents are biseparable, and the complete matrix is reconstructed. Its original convex roof is zero, including p=1.

**Theorem 1.11 (noisy parameter data).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_parameter_data`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_parameter_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.12 (noisy triangle).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.13 (noisy witness means).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_witness_means`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_witness_means` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.14 (twoMeanOptimum pos).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.twoMeanOptimum_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.twoMeanOptimum_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.15 (qIndex card).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.qIndex_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.qIndex_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.16 (noisy optimum zero).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_optimum_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_optimum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.high_noise_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.high_noise_reconstruction`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.low_noise_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.low_noise_reconstruction`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_means`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_optimum_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_parameter_data`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_triangle`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_witness_means`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.noisy_witness_optimum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.qIndex_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.source_average_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.threshold_constituents_biseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.twoMeanOptimum_pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.two_mean_strict_witness_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.witness_value_affine`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates](CutStates.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/Foundations](Foundations.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages](MatrixAverages.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum](ObservableOptimum.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/TwoMeanBound](TwoMeanBound.md)
