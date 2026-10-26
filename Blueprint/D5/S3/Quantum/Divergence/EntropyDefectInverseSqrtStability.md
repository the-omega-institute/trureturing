# Entropy defect and inverse-square-root stability

## Abstract

Actual quantum entropy loss bounds supported inverse-square-root intertwining in L2.

**Theorem 1.1 (A fourth-root L2 estimate on the actual supported model).**

Lean statement: `D5/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability.entropy_defect_inverse_sqrt_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability.entropy_defect_inverse_sqrt_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

Let Phi be a channel between arbitrary finite nonempty quantum systems, and let rho and sigma be density states with support of rho contained in support of sigma. Form their canonical supported relative-modular model M, with matrices A and B, map V and normalized vectors xi and eta. For every positive real m with mI <= A and mI <= B, set d to cfc(1/sqrt)(A) xi minus V cfc(1/sqrt)(B) eta. The square root of the real part of star(d) dot d is at most 4/(pi sqrt(m)) times Delta to the power one quarter, where Delta is the actual finite trace-log relative entropy of rho and sigma minus that of their channel images. The floor assumptions concern the supported carriers; the physical density states may be singular.

The proof consumes the full positive-axis entropy resolvent energy budget. Mathlib's positive-power integrand gives the inverse-power integral after division by the positive spectral value. Substitution t=x/(1-x), the Beta integral and Gamma reflection evaluate the normalizer as pi/sin(pi alpha), giving pi at alpha=1/2. Finite spectral sums give the inverse-power identity and Bochner integrability; linear maps transfer them through V and the equivalence to EuclideanSpace Complex. All subsequent norms are L2. The positive semidefinite difference I minus V adjoint V gives contraction. Quadratic coercivity under the common spectral floor and Cauchy-Schwarz bound each resolvent vector by 1/m, hence their difference by 2/m. Splitting the weighted integral at a positive cutoff a gives 4 sqrt(a)/m plus sqrt(Delta)/sqrt(a), before division by pi. For positive Delta, choose a=m sqrt(Delta)/4. If Delta is zero, nonnegative energy vanishes almost everywhere and the integral error is exactly zero.

The scalar integral and near/tail estimates are consumed helpers. This is a repository derivation using existing suppliers and pinned Mathlib analysis, with no claim of literature novelty. Identifying d with a physical Hilbert-Schmidt error requires additional spectral weights and a support-column projection; this theorem makes no such identification and asserts no trace-distance recovery estimate.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/EntropyDefectInverseSqrtStability.entropy_defect_inverse_sqrt_stability`
- Dependency: [D5/S3/Quantum/Divergence/EntropyDefectResolventIntegralBudget](EntropyDefectResolventIntegralBudget.md)
