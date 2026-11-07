# Noisy GHZ: actual finite roofs and observable optima

## Abstract

Actual all-cut noisy-GHZ bounds, attained two-observable minima and the original single-witness conjugate.

Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.

Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.

Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.

The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.

**Theorem 1.1 (Independent-coordinate character orthogonality).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phaseCharacter_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phaseCharacter_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every natural d and every coefficient vector on Fin d, the full finite sum over independent ZMod 3 coordinates is 3^d for the zero vector and zero otherwise.

**Theorem 1.2 (The zero ordered-pair mode).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pairCoefficient_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pairCoefficient_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The coefficient vector of an ordered pair vanishes precisely on diagonal pairs.

**Theorem 1.3 (Ordered-pair character average).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_phase_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_phase_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The finite average keeps precisely the diagonal ordered pairs.

**Theorem 1.4 (Distinct nonzero coordinate characters).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pairCoefficient_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pairCoefficient_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Two pair coefficient vectors agree precisely when both pairs are diagonal or when the ordered pairs themselves agree. This uses independent coordinate vectors, not scalar index differences.

**Theorem 1.5 (The full character Gram identity).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_cross_phase_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_cross_phase_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The cross-character average vanishes except for identical nonzero modes or two zero modes. The identity is symbolic in arbitrary d.

**Theorem 1.6 (Normalization of the GHZ vector).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For positive party count and positive local dimension, the original ghz vector has sum of squared complex amplitudes one.

**Theorem 1.7 (The qubit support boundary).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qubit_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qubit_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

When d=2 every computational word uses at most two symbols, so the actual supportProjector equals the identity.

**Theorem 1.8 (The qubit witness boundary).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qubit_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qubit_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The original witness is I/2 minus the GHZ projector at d=2. This is an operator identity and does not assert a qubit convex-roof formula.

**Theorem 1.9 (The universal all-cut overlap inequality).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.biseparable_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.biseparable_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every actual IsBiseparable vector, d times its GHZ expectation is at most its support-projector expectation. The proof keeps the source factorization across an arbitrary nonempty proper cut.

**Theorem 1.10 (Computational product states).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.computational_biseparable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.computational_biseparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Every computational basis vector factors across a nonempty proper cut when n is at least two.

**Theorem 1.11 (Well-defined pure geometric measure).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pure_measure_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pure_measure_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual biseparable-overlap supremum is nonempty and bounded for unit vectors, and the pure measure lies between zero and one.

**Theorem 1.12 (Well-defined finite convex roof).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.density_measure_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.density_measure_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Every actual density state has a finite normalized ensemble supplied by the existing density_ensemble theorem. The ensemble-value set is bounded below, and its infimum is nonnegative.

**Theorem 1.13 (Finite positive-metric supporting family).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.metric_roof_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.metric_roof_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For positive metric coefficients satisfying the displayed inverse constraint, the actual finite-ensemble roof bounds the corresponding affine combination of the G and P means. No scalar roof is assumed.

**Theorem 1.14 (Nonsingular finite supporting lines).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.supporting_line`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.supporting_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Every parameter t at least one supplies a finite affine lower bound. The coincident-means endpoint is derived from these finite lines, without substituting an infinite metric coefficient.

**Theorem 1.15 (The universal analytic certificate).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.affine_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.affine_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every density state with n,d at least three, E is at least minus (d-1)/(d(d-2)) times the W mean, plus 1/(d^2(d-2)) times the Q mean, minus the same constant.

**Theorem 1.16 (The feasible two-mean triangle).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.means_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.means_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual density-state means f=Tr(sigma G) and y=Tr(sigma P) satisfy zero at most f at most y at most one.

**Theorem 1.17 (The universal two-mean lower bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Every actual density state obeys E(sigma) at least twoMeanOptimum d f y. The definition retains the zero branch when d*f is at most y and the source radical branch otherwise.

**Theorem 1.18 (The all-cut pure two-mean bound).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pure_two_mean_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pure_two_mean_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The same two-mean lower bound applies to each normalized pure vector and its actual supremum over all biseparable cuts.

**Theorem 1.19 (Actual finite roof competitors).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.finite_ensemble_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.finite_ensemble_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Any finite normalized family of unit amplitudes is explicitly reindexed to Fin k and enters the original roof set, giving its weighted entanglement as an upper bound.

**Theorem 1.20 (Zero roof of finite biseparable ensembles).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.biseparable_ensemble_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.biseparable_ensemble_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

A concrete normalized finite family of genuinely biseparable vectors has zero actual convex roof.

**Theorem 1.21 (The source constant-sector pure optimizer).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.chi_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.chi_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual chi vector has one optimalAlpha amplitude and d-1 optimalBeta amplitudes. Its norm is one, its P and G means are one and F, and its all-cut pure measure equals the complete optimum, including F=1/d and F=1.

**Theorem 1.22 (The measured means W,Q).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.observable_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.observable_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every density state, y=1-q and f=(1-q)/d-w. Thus the two G,P means encode exactly the two W,Q measurements.

**Theorem 1.23 (Attained all-state two-mean minimum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Every feasible pair has an actual density operator and the explicit three-component normalized ensemble twoMeanWeights/twoMeanStates. Their matrix sum, both means, average entanglement and exact roof are proved. The zero branch uses computational products, including qWord=|0,1,2,0,...>; the positive branch mixes chi with qWord. This optimizer is not asserted to be the noisy matrix.

**Theorem 1.24 (The complete original single-witness optimum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

On the full interval -(d-1)/d through 1/d, epsilonWitness equals twoMeanOptimum d (1/d-w) 1. epsilonWitness uses the original hatE two-vector supremum, and epsilonO is its exact specialization at witnessValue. The proof covers both spectral endpoints and the nonnegative-w zero interval using actual finite optimizers and finite supporting slopes.

**Theorem 1.25 (Actual cut product vectors).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutProduct_biseparable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutProduct_biseparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every nonempty proper cut and every unit local vector u, cutProduct embeds u tensor conjugate(u) into the original computational word space and satisfies the original IsBiseparable factorization predicate.

**Theorem 1.26 (Normalization of the source cut constituents).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutState_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutState_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

Every source cutState has norm one whenever alpha squared plus (d-1) beta squared is one, for every unit local u and every nonempty proper cut.

**Theorem 1.27 (Genuine all-cut entanglement of each constituent).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutState_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutState_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For the source optimal amplitudes and every unit u, the actual cutState has means (F,1), norm one and genuine all-cut pure entanglement twoMeanOptimum d F 1. A product across the specified cut attains overlap alpha; the universal all-cut bound gives the reverse inequality.

**Theorem 1.28 (Number of anchored bipartitions).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.sourceCut_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.sourceCut_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The nonempty subsets excluding the first party have exactly K=2^(n-1)-1 elements; their complements are the anchored representatives used by the finite phase ensemble.

**Theorem 1.29 (Full disjoint support enumeration).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

A proved bijection enumerates words using at most two symbols by constants plus anchored cuts times distinct ordered symbol pairs. Its cardinal is d+K*d*(d-1).

**Theorem 1.30 (Actual support-projector trace).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The real rank formula is the trace of the original complex-matrix supportProjector, for arbitrary positive party count.

**Theorem 1.31 (Strict support-rank inequalities).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For n,d at least three, d<R<M. The strict upper bound uses the actual computational word qWord outside P.

**Theorem 1.32 (The complete truncated radical).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.twoMeanOptimum_max`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.twoMeanOptimum_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

On the closed triangle zero at most f at most y, the piecewise optimum equals the squared positive part of sqrt((d-1)f)-sqrt(y-f), divided by d.

**Theorem 1.33 (The actual disjoint support-matrix decomposition).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_projector_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_projector_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The original complex matrix P equals the constant-word projector C plus the sum of the off-constant projectors for all anchored bipartitions. This is a full matrix equality, not only a dimension count.

**Theorem 1.34 (The full finite basis-average matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.basis_average_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.basis_average_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The d actual chi projectors average to F*G+(1-F)/(d-1)*(C-G), with exact arbitrary-d coefficients and endpoint domains.

**Theorem 1.35 (The full finite phase-average matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phase_average_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phase_average_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For each nonempty proper cut, the 3^d actual cutState projectors average to F*G+(1-F)/(d*(d-1))*T_A. All unwanted matrix entries cancel by independent-coordinate character orthogonality, for arbitrary d.

**Theorem 1.36 (Exact qutrit parameter checkpoint).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_source_arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_source_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

At n=d=3, M=27, K=3, R=21, k=8/9 and p_W=3/4. This arithmetic checkpoint alone does not prove a matrix decomposition.

**Theorem 1.37 (Exact qutrit radical value).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_two_mean_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_two_mean_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The radical branch at f=23/36 and y=11/12 equals (14-sqrt(115))/27. Identifying it with the noisy-state roof additionally requires the full actual matrix ensemble.

**Theorem 1.38 (Exact noisy-matrix means).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_means`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_means` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual complex-matrix real traces are f=1-p+p/M and y=1-p+p*R/M.

**Theorem 1.39 (The affine noisy witness).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_value_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_value_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The original witnessValue is exactly -(d-1)/d+k*p, with the defined source slope.

**Theorem 1.40 (The original noisy single-witness optimum).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_witness_optimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_witness_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every physical p the original epsilonO equals the full feasible-interval optimum at the actual witness trace. It is bridged through the defining hatE, without the disputed all-real-slope antecedent formula.

**Theorem 1.41 (Strict two-observable advantage).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_strict_witness_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_strict_witness_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

On the full means triangle, y<1 and negative witness imply strict improvement over the complete original single-witness conjugate. The proof compares radicals with their sign conditions and uses no singular endpoint metric.

**Theorem 1.42 (The complete supported source average).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.source_average_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.source_average_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The finite combination S_F of J_F and all anchored H_A,F equals F*G+(1-F)/(R-1)*(P-G), as a full matrix identity.

**Theorem 1.43 (The complete low-noise matrix reconstruction).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.low_noise_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.low_noise_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For 0<=p<=p_W, lowNoiseWeights and lowNoiseStates reconstruct every entry of rho(p). Their index consists of d basis vectors, K*3^d cut-phase vectors, and the actual computational Q sector.

**Theorem 1.44 (An actual attaining low-noise ensemble).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.low_noise_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.low_noise_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The displayed weights are nonnegative and sum to one, every constituent is unit, their projectors reconstruct the actual noisy matrix, and their mean pure measure equals the two-mean value and the actual finite convex roof. The p=0 and p=p_W endpoints are included.

**Theorem 1.45 (Actual cut products at the threshold).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.threshold_constituents_biseparable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.threshold_constituents_biseparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

At p_W the optimal amplitudes are alpha=1 and beta=0. Every constituent genuinely factorizes across its displayed nonempty proper cut or is a computational product; zero roof is not used to infer factorization.

**Theorem 1.46 (Full high-noise matrix reconstruction).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.high_noise_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.high_noise_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For p_W<=p<=1 the explicit finite highNoiseWeights and highNoiseStates mix the threshold ensemble with the computational I/M ensemble, with lambda=(1-p)/(1-p_W).

**Theorem 1.47 (A finite biseparable high-noise ensemble).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.high_noise_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.high_noise_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

All high-noise weights are nonnegative and normalized, all actual constituents are biseparable, and the complete matrix is reconstructed. Its original convex roof is zero, including p=1.

**Theorem 1.48 (The entire noisy-GHZ exact convex roof).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_exact_roof`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_exact_roof` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every n,d>=3 and 0<=p<=1, the actual finite-ensemble convex roof is twoMeanOptimum d f y and equals the truncated-radical source formula. Both finite constructions supply genuine attainment, rather than only matching two means.

**Theorem 1.49 (The exact physical threshold).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_threshold_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_threshold_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The source threshold is M*(d-1)/(M*(d-1)+R-d), strictly between zero and one.

**Theorem 1.50 (The exact interior single-witness value).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_single_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_single_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

At p_star=(d-2)^2/(T*k), the probability lies strictly between zero and p_W, the witness is w_star, and the original epsilonO is e_star=1/((d-1)^3+1).

**Theorem 1.51 (The entire strict noisy interval).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_strict_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_strict_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

For every 0<p<p_W the complete original epsilonO is strictly less than the two-mean optimum, which equals the actual noisy roof.

**Theorem 1.52 (Equality and the common zero region).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_gap_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_gap_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The witness optimum equals the actual roof at p=0. Both are zero throughout p_W<=p<=1; the finite biseparable ensemble is supplied by high_noise_attainment.

**Theorem 1.53 (A strictly stronger universal certificate at p_star).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_certificate_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_certificate_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual affine certificate gives e_star+h*p_star*(1-R/M) as a roof lower bound, and this is strictly greater than e_star. Positivity uses the genuine support rank R<M.

**Theorem 1.54 (The exact 90-component qutrit roof).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_exact_ensemble`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_exact_ensemble` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

At n=d=3 and p=3/8, the universal ensemble specializes to three basis components of weight 11/360, 81 cut-phase components of weight 11/1080 and six Q components of weight 1/72. Complete amplitudes are lowNoiseStates at F=23/33. Their full matrix is I/72+5*G/8, their average and actual roof equal (14-sqrt(115))/27, strictly greater than 13/108, which is greater than epsilonO=1/9.

**Theorem 1.55 (The manuscript support-rank formula).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_binomial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_binomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual two-symbol support rank is also d+choose(d,2)*(2^n-2), with exact natural-number arithmetic.

**Theorem 1.56 (Attainment at the left spectral endpoint).**

Lean statement: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_left_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_left_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen (2023). *General framework for genuine multipartite entanglement detection*. DOI: [10.1103/PhysRevA.107.052405](https://doi.org/10.1103/PhysRevA.107.052405). URL: <https://arxiv.org/abs/2211.05563v1>.

*Commentary.*

The actual normalized GHZ vector has all-cut pure measure (d-1)/d, witness expectation -(d-1)/d, and the original conjugate has the same endpoint value.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.affine_certificate`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.basis_average_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.biseparable_ensemble_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.biseparable_overlap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.chi_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.computational_biseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutProduct_biseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutState_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.cutState_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.density_measure_nonneg`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.finite_ensemble_upper`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_left_endpoint`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.ghz_unit`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.high_noise_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.high_noise_reconstruction`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.low_noise_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.low_noise_reconstruction`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.means_triangle`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.metric_roof_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_exact_roof`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_gap_endpoints`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_means`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_strict_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.noisy_witness_optimum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.observable_correspondence`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pairCoefficient_eq_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pairCoefficient_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_cross_phase_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pair_phase_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phaseCharacter_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.phase_average_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pure_measure_bounds`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.pure_two_mean_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qubit_support`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qubit_witness`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_exact_ensemble`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_source_arithmetic`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.qutrit_two_mean_value`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.sourceCut_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.source_average_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_certificate_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.star_single_witness`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_projector_decomposition`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_binomial`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_bounds`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_rank_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.support_trace`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.supporting_line`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.threshold_constituents_biseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.twoMeanOptimum_max`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.two_mean_strict_witness_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_optimum`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_threshold_formula`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.witness_value_affine`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap](NoisyGhzWitnessBoundGap.md)
