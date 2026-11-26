# Coincidence of symmetric hypercube quantum-walk limits

## Abstract

For every family of symmetric hypercube walks, a common weak limit exists exactly when all fixed-order CT–DT Walsh gaps vanish and all corresponding CT collision coefficients converge.

In arXiv:2611.31635v1, Section 5, printed p. 14, Ide, Konno and Mano write, “It is therefore an open problem to find a necessary and sufficient condition for the coincidence of the scaling limits.” At each dimension d choose nonnegative weights w_d(h) for 0 ≤ h ≤ d whose sum is one. The increment law is w_d(|y|)/choose(d,|y|). Both walks start at the origin. Take their respective Cesàro limits at fixed d, then push the position laws forward by normalized Hamming weight |x|/d. Write ν_{C,d} and ν_{D,d} for the resulting probability laws on [0,1]. All displayed arrows are along the full sequence d → ∞ and denote weak convergence for laws. The source starts at d ≥ 3. Extending the weights at the finitely many smaller dimensions has no effect on these limits.

**Theorem 1.1 (Existence of a common weak limit).**

$$(\exists \pi, (\nu_{C,d} \to \pi \land \nu_{D,d} \to \pi)) \iff \forall k>0, (\Delta_{d,k} \to 0 \land (\exists m, B_{d,k} \to m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.exists_common_shell_weakLimit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

B_{d,k} is the CT coefficient and Δ_{d,k} is CT minus DT. For fixed k and d ≥ k their normalized double sums use binomial weights choose(d−k,i) choose(k,j)/2^d. The CT coefficient counts equal numerical eigenvalues at shells i+j and i+k−j. The gap uses (1−ρ_k)/(2(1−ρ_{i+j}²)) at equal interior eigenvalues and zero otherwise. Both equal endpoints contribute one to the CT and DT coefficients and zero to the gap. At k = 0, B_{d,0} = 1 and Δ_{d,0} = 0.

Coordinate permutations preserve both time-averaged laws. Sampling bounds compare their Walsh coefficients with their shifted radial moments, with error at most k(k−1)/d per law. Compactness of the probability measures on [0,1] and the shifted moment criterion produce CT convergence from convergence of all B_{d,k}. The gap condition transfers this limit to DT. Conversely, both laws converging to π gives the same shifted moments, so every gap vanishes and every CT coefficient converges.

**Theorem 1.2 (Coincidence when one law converges).**

$$(\nu_{C,d} \to \pi \lor \nu_{D,d} \to \pi) \implies ((\nu_{C,d} \to \pi \land \nu_{D,d} \to \pi) \iff \forall k>0, \Delta_{d,k} \to 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.common_shell_weakLimit_iff_gap` (`✓ std3`). ∎

*Resolves.* `Problems/ide-konno-mano-2026-hypercube-walk-limit-coincidence` (proved) by `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.common_shell_weakLimit_iff_gap`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ide-konno-mano-2026-hypercube-walk-limit-coincidence","declaration_gid":"D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.common_shell_weakLimit_iff_gap","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

For any probability law π on [0,1], if either sequence converges weakly to π, the other converges to π exactly when every fixed positive-order gap vanishes. If existence is unknown, vanishing gaps characterize agreement in the limit on every continuous test, as formalized by shell_continuous_tests_gap_iff. As an example of the existence distinction, take deterministic zero increments in even dimensions and deterministic all-ones increments in odd dimensions. The two laws agree at each dimension, but alternate between a point mass at 0 and an equal mixture of the point masses at 0 and 1.

**Theorem 1.3 (Collision limits identify the limiting moments).**

$$\nu_{C,d} \to \pi \implies \forall k, B_{d,k} \to \int_{[0,1]}(1-2x)^{k} d\pi(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.tendsto_shell_collisions_to_shiftedMoment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

For every natural k, the collision limit is the kth shifted moment of the CT limit. This also identifies the common limit uniquely when the gaps vanish.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.common_shell_weakLimit_iff_gap`
- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.exists_common_shell_weakLimit_iff`
- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.tendsto_shell_collisions_to_shiftedMoment`
- Dependency: [D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ExchangeableLaws](ExchangeableLaws.md)
- Dependency: [D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients](ShellCoefficients.md)
