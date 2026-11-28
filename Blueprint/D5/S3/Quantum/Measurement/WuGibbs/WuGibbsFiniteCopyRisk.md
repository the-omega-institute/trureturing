# Finite-copy testing against Wu’s Gibbs state

## Abstract

The physical one-mode Wu deficit bounds the probability gap of every collective binary effect at every finite copy count.

**Theorem 1.1 (Trace distance from ordinary square-root affinity).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk.traceNorm_sub_half_le_sqrt_one_sub_affinity_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk.traceNorm_sub_half_le_sqrt_one_sub_affinity_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex positive semidefinite matrices ρ and σ of ordinary trace one on the same finite index set, put A = Re Tr(√ρ √σ), using the positive matrix square roots. Then ‖ρ − σ‖₁/2 ≤ √(1 − A²), where ‖·‖₁ is the trace norm. The bound includes singular states. The sum and difference of the two roots give a symmetrized product for ρ − σ, and the Hilbert–Schmidt product bound controls its trace norm.

**Theorem 1.2 (Collective binary probability gap from the one-mode deficit).**

Lean statement: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk.collective_effect_gap_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk.collective_effect_gap_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let h = β/2 ≥ 0 and let σₕ = gibbs(h) be the one-mode Gibbs density in the normalization of Wu, arXiv:2610.33686v1, §3.1. For every complex positive semidefinite trace-one qubit ρ, put A = Re Tr(√ρ √σₕ), δ = energy(h,ρ) − sharpCoefficient(h) × entropy(h,ρ), c = exactAffinityCoefficient(h), and L = max(0, 1 − √(δ/c)). The physical affinity bound gives L ≤ A. For every natural n, put D = ρ⊗ⁿ − σₕ⊗ⁿ using the actual tensor powers. The theorem `D5.S3.Quantum.Measurement.WuGibbsFiniteCopyRisk.collective_effect_gap_le` gives, for every effect E on these copies with E and I − E positive semidefinite, |Re Tr(ED)| ≤ ‖D‖₁/2 ≤ √(1 − (Aⁿ)²) ≤ √(1 − (Lⁿ)²). The square-root affinity of the two tensor powers is Aⁿ. Either outcome of the binary measurement {E, I − E} has this absolute probability gap. With equal priors, half the bound controls the success advantage over random guessing. At n = 0 the tensor powers coincide and the bounds are zero.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk.collective_effect_gap_le`
- Truth anchor: `D5/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk.traceNorm_sub_half_le_sqrt_one_sub_affinity_sq`
- Dependency: [D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability](../../Foundation/HilbertSchmidtTraceStability.md)
- Dependency: [D5/S3/Quantum/Measurement/AdvantageQuantumNonSimulability](../AdvantageQuantumNonSimulability.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/DiamondBounds](../Auric/DiamondBounds.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuQubitSharpTwoPhysical](../../Semigroups/WuQubitSharpTwoPhysical.md)
