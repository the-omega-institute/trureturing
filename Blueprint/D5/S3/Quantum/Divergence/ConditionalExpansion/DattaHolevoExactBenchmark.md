# Exact Datta–Holevo filter benchmark

## Abstract

The complementary depolarizing filter has exact conditional expansion and heralded recovery coefficients.

**Theorem 1.1 (Exact conditional expansion).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DattaHolevoExactBenchmark.sharp_family_expansion_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/DattaHolevoExactBenchmark.sharp_family_expansion_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d ≥ 2 be the input dimension and 0 < a < 1. With P the normalized Bell projector, set b = (d² − a)/(d² − 1) and G = aP + b(I − P). For any channel N whose action is the normalized filter action G¹ᐟ²(X ⊗ I/d)G¹ᐟ², the conditional expansion infimum equals harmonicParameter d a = a(d² − a)/(1 + (d² − 2)a) for every γ ≥ 1 and both orthogonality flags, over arbitrary finite references. The inverse marginals agree by factor-swap symmetry, so the filter lower bound and Bell-kernel upper bound coincide.

The filter is from Datta–Holevo, arXiv:quant-ph/0510145, §3, Eqs. (11) and (16). The finite-reference conditional expansion coefficient is Hirche–George–Nuradha–Wilde, arXiv:2608.27171v1, Eq. (2.42).

**Theorem 1.2 (Exact attained heralded recovery).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DattaHolevoExactBenchmark.sharp_family_recovery_sup_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/DattaHolevoExactBenchmark.sharp_family_recovery_sup_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, the supremum of probabilities of finite trace-nonincreasing Kraus operations composing with N to p times the identity on all input matrices is a. The companion theorem sharp_family_recovery_attains constructs coordinate slices of the inverse square root filter with effect aG⁻¹ ≤ I, giving the success branch aX. The existing recovery upper bound then gives optimality.

The related complementary-channel replacement-weight characterization follows from Bény–Oreshkov, arXiv:1103.0649v3, Theorem 2.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DattaHolevoExactBenchmark.sharp_family_expansion_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DattaHolevoExactBenchmark.sharp_family_recovery_sup_eq`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellKernelUpperBound](FilteredBellKernelUpperBound.md)
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryLowerBound](HeraldedRecoveryLowerBound.md)
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/SharpFilteredRecoveryFactor](SharpFilteredRecoveryFactor.md)
