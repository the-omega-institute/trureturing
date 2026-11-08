# Noisy GHZ: exact roof and strict gaps

## Abstract

Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.

Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.

Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.

Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.

The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.

**Theorem 1.1 (The entire noisy-GHZ exact convex roof).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_exact_roof`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_exact_roof` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every n,d>=3 and 0<=p<=1, the actual finite-ensemble convex roof is twoMeanOptimum d f y and equals the truncated-radical source formula. Both finite constructions supply genuine attainment, rather than only matching two means.

**Theorem 1.2 (The exact physical threshold).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_threshold_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_threshold_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The source threshold is M*(d-1)/(M*(d-1)+R-d), strictly between zero and one.

**Theorem 1.3 (The exact interior single-witness value).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_single_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_single_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

At p_star=(d-2)^2/(T*k), the probability lies strictly between zero and p_W, the witness is w_star, and the original epsilonO is e_star=1/((d-1)^3+1).

**Theorem 1.4 (The entire strict noisy interval).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_strict_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_strict_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every 0<p<p_W the complete original epsilonO is strictly less than the two-mean optimum, which equals the actual noisy roof.

**Theorem 1.5 (Equality and the common zero region).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_gap_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_gap_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The witness optimum equals the actual roof at p=0. Both are zero throughout p_W<=p<=1; the finite biseparable ensemble is supplied by high_noise_attainment.

**Theorem 1.6 (A strictly stronger universal certificate at p_star).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_certificate_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_certificate_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual affine certificate gives e_star+h*p_star*(1-R/M) as a roof lower bound, and this is strictly greater than e_star. Positivity uses the genuine support rank R<M.

**Theorem 1.7 (The exact 90-component qutrit roof).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_exact_ensemble`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_exact_ensemble` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

At n=d=3 and p=3/8, the universal ensemble specializes to three basis components of weight 11/360, 81 cut-phase components of weight 11/1080 and six Q components of weight 1/72. Complete amplitudes are lowNoiseStates at F=23/33. Their full matrix is I/72+5*G/8, their average and actual roof equal (14-sqrt(115))/27, strictly greater than 13/108, which is greater than epsilonO=1/9.

**Theorem 1.8 (The manuscript support-rank formula).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_binomial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_binomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual two-symbol support rank is also d+choose(d,2)*(2^n-2), with exact natural-number arithmetic.

**Theorem 1.9 (Attainment at the left spectral endpoint).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_left_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_left_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual normalized GHZ vector has all-cut pure measure (d-1)/d, witness expectation -(d-1)/d, and the original conjugate has the same endpoint value.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_left_endpoint`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_exact_roof`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_gap_endpoints`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_strict_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_exact_ensemble`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_certificate_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_single_witness`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_binomial`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_threshold_formula`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates](NoisyGhzExactRoof/CutStates.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/Foundations](NoisyGhzExactRoof/Foundations.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages](NoisyGhzExactRoof/MatrixAverages.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles](NoisyGhzExactRoof/NoisyEnsembles.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum](NoisyGhzExactRoof/ObservableOptimum.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/TwoMeanBound](NoisyGhzExactRoof/TwoMeanBound.md)
