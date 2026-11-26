# Parity reduction of Wu’s cubic inequality

## Abstract

The two-mode cubic deficit on physical parity blocks is a weighted average of four diagonal deficits.

**Theorem 1.1 (Cubic deficit on a parity orbit).**

Lean statement: `D5/S3/Quantum/Semigroups/WuParityOrbit.cubicDeficit_parity_orbit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuParityOrbit.cubicDeficit_parity_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

In occupation order (00, 01, 10, 11), put Hermitian blocks A and B on the ordered sectors (00, 11) and (01, 10). Let v and w be their eigenvalues in the orders given by their unitary eigenframes, and let p and q be the squared moduli of the respective (0, 1) entries. The cubic deficit uses the real logarithm in its trace expression, which is the Gibbs entropy term on positive semidefinite inputs. For any r ≥ 1 and c ∈ ℝ, the deficit equals the weighted sum of the deficits on the four physical diagonal assignments of v and w. The weights for swapping neither block, B alone, A alone, or both are (1 − p)(1 − q), (1 − p)q, p(1 − q), and pq.

With matrix units indexed from zero, the lowering jumps are E₀₂ + E₁₃ and −E₀₁ + E₂₃. The interference terms vanish on parity blocks. Each surviving mixed product uses one diagonal moment from each block, so independent swaps reproduce it in expectation. The anticommutator and log D terms use single diagonal moments. The trace of M³ log M³ and the total cubic mass depend only on the eigenvalues.

**Theorem 1.2 (Cubic inequality for parity-preserving observables).**

Lean statement: `D5/S3/Quantum/Semigroups/WuParityOrbit.cubic_inequality_of_commute_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuParityOrbit.cubic_inequality_of_commute_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

In Wu v1, Remark 3.15, eqs. (3.54)–(3.55), take exponent three and two signed CAR modes with the same Gibbs odds r³, where r = exp(β/3) ≥ 1. Let X be positive semidefinite and commute with diag(1, −1, −1, 1). Set M = G X G with G = D^(1/6) for the product Gibbs density D. With ordinary trace, the signed Dirichlet term (9/8) Re Tr(M² G ℒᵣ(X) G) bounds α(r)[Re Tr(M³(log M³ − log D)) − t log t], where t = Re Tr(M³) and α(1) = 1/2. The matrix logarithms use the real functional calculus with Real.log 0 = 0.

The diagonal Gibbs factor preserves the parity blocks of X. Each of the four diagonal assignments of the block spectra of M satisfies the occupation-conditioned cubic bound. The orbit identity averages these endpoint bounds, including for singular blocks.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuParityOrbit.cubicDeficit_parity_orbit`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuParityOrbit.cubic_inequality_of_commute_parity`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicConditionalTensorization](WuCubicConditionalTensorization.md)
