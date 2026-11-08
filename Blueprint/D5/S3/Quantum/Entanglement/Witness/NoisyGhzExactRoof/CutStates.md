# Noisy GHZ: CutStates

## Abstract

Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.

Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.

Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.

Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.

The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.

**Theorem 1.1 (Actual cut product vectors).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutProduct_biseparable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutProduct_biseparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every nonempty proper cut and every unit local vector u, cutProduct embeds u tensor conjugate(u) into the original computational word space and satisfies the original IsBiseparable factorization predicate.

**Theorem 1.2 (Normalization of the source cut constituents).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutState_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutState_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Every source cutState has norm one whenever alpha squared plus (d-1) beta squared is one, for every unit local u and every nonempty proper cut.

**Theorem 1.3 (Genuine all-cut entanglement of each constituent).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutState_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutState_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For the source optimal amplitudes and every unit u, the actual cutState has means (F,1), norm one and genuine all-cut pure entanglement twoMeanOptimum d F 1. A product across the specified cut attains overlap alpha; the universal all-cut bound gives the reverse inequality.

**Theorem 1.4 (Number of anchored bipartitions).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The nonempty subsets excluding the first party have exactly K=2^(n-1)-1 elements; their complements are the anchored representatives used by the finite phase ensemble.

**Theorem 1.5 (Full disjoint support enumeration).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_rank_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_rank_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

A proved bijection enumerates words using at most two symbols by constants plus anchored cuts times distinct ordered symbol pairs. Its cardinal is d+K*d*(d-1).

**Theorem 1.6 (Actual support-projector trace).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The real rank formula is the trace of the original complex-matrix supportProjector, for arbitrary positive party count.

**Theorem 1.7 (Strict support-rank inequalities).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_rank_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_rank_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For n,d at least three, d<R<M. The strict upper bound uses the actual computational word qWord outside P.

**Theorem 1.8 (sum on embedding).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sum_on_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sum_on_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.9 (pushVector apply).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.pushVector_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.pushVector_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.10 (pushVector off).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.pushVector_off`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.pushVector_off` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.11 (phaseVector unit).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.phaseVector_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.phaseVector_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.12 (phaseVector pair).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.phaseVector_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.phaseVector_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.13 (sourceCut nonempty).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.14 (sourceCut complement).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.15 (supportIndexWord injective).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.16 (supportIndexWord supported).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.17 (supportIndexWord surjective).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

**Theorem 1.18 (basis projector sum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.basis_projector_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.basis_projector_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.basis_projector_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutProduct_biseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutState_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.cutState_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.phaseVector_pair`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.phaseVector_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.pushVector_apply`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.pushVector_off`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_complement`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sourceCut_nonempty`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.sum_on_embedding`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_supported`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.supportIndexWord_surjective`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_rank_bounds`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_rank_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.support_trace`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/Foundations](Foundations.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum](ObservableOptimum.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/TwoMeanBound](TwoMeanBound.md)
