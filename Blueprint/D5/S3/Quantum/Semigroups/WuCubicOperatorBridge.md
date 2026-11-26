# The repeated-middle cubic operator inequality

## Abstract

The cubic operator Dirichlet term bounds the Gibbs entropy for unnormalized repeated-middle spectra of two equal-cap CAR modes.

**Theorem 1.1 (Operator Dirichlet bound for cubic Gibbs entropy).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicOperatorBridge.source_operator_inequality_unnormalized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicOperatorBridge.source_operator_inequality_unnormalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

In Wu v1, Remark 3.15, eqs. (3.54)–(3.55), take exponent three, two signed CAR modes and equal caps μ₁⁴ = μ₂⁴ = r³ with r = exp(β/3) ≥ 1. For every such real r, every complex frame U with UᴴU = I and UUᴴ = I, and all real m, n, L with 0 ≤ m ≤ n ≤ L, set M = U diag(m, n, n, L) Uᴴ. The rows of U are indexed by the two-mode occupation basis and its four columns by the spectral levels. The product Gibbs density D has one-mode weights 1/(1 + r³) and r³/(1 + r³). The positive diagonal G satisfies G⁶ = D. With X = G⁻¹ M G⁻¹ we have M = G X G.

With the ordinary unnormalized trace, the Dirichlet term (9/8) Re Tr(M² G ℒᵣ(X) G) is at least α(r) times the Gibbs entropy [Re Tr(M³ (log M³ − log D)) − Re Tr(M³) log(Re Tr(M³))]. Here ℒᵣ is the signed CAR generator in the positive Dirichlet sign convention and α(r) is Wu’s cubic coefficient with α(1) = 1/2. The matrix logarithms use the real continuous functional calculus with Lean’s Real.log 0 = 0, including when a level vanishes.

Modular conjugation gives the weighted cubic spectral energy from the operator Dirichlet term. Unitary covariance and diagonal evaluation of the functional calculus give the Gibbs entropy in the same spectral coordinates. The one-mode bound and the repeated-middle deficit lower bound give the comparison at top level one.

Scaling the spectrum by c ≥ 0 multiplies both terms by c³. For c > 0, the log(c³) contributions from the level sum and the total-mass correction cancel in the entropy. For L > 0 the proof uses the normalized levels (m/L, n/L, n/L, 1) and scales the comparison by L³. When L = 0, the order forces m = n = 0, so M = X = 0 and both sides vanish.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicOperatorBridge.source_operator_inequality_unnormalized`
- Dependency: [D5/S3/Quantum/Semigroups/WuOneModeCubic](WuOneModeCubic.md)
