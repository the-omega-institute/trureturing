# Rank-two spectator compression

## Abstract

Exact cold cost and rank-two purity under normalized spectator compression.

In Wu’s signed-spin setting, use occupation order (spectator, cold), ordinary traces, and the cold jump J_c = Z ⊗ e with e = |0⟩⟨1|. Write Q = Tr_s(A)/2, C = I ⊗ Q, and H = A − C. The cold quadratic is k(B) = c Re Tr(B²) + q Re Tr(B²P₀) − K Re Tr(B J_c B J_c†). Here P₀ = J_c J_c†, P₁ = J_c† J_c, and k_* = c − (K − q)²/(4K) for K > 0.

**Theorem 1.1 (Cold occupation projections).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.cold_projectors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.cold_projectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The two products of the signed jump with its adjoint are the lifted vacuum and occupied projections. Their sum is I.

**Theorem 1.2 (Positive cold marginal).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldMarginal_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldMarginal_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every positive semidefinite A, the partial trace over the spectator is positive semidefinite, and scaling it by 1/2 gives a positive semidefinite Q.

**Theorem 1.3 (Trace pairing with cold observables).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_mul_liftCold`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_mul_liftCold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For arbitrary complex A and cold matrix R, Tr(A(I ⊗ R)) = Tr((Tr_s A)R).

**Theorem 1.4 (Marginal of a lifted observable).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldMarginal_liftCold`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldMarginal_liftCold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The normalized spectator partial trace of I ⊗ R is R.

**Theorem 1.5 (Positive cold lift).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.liftCold_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.liftCold_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

If R is positive semidefinite, then I ⊗ R is positive semidefinite.

**Theorem 1.6 (Zero partial trace of the remainder).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.partialTrace_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.partialTrace_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For arbitrary complex A, Tr_s H = 0, so the trace pairing of H with any lifted cold observable vanishes.

**Theorem 1.7 (Trace purity under compression).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_remainder_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_remainder_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For arbitrary complex A, Re Tr(H²) = Re Tr(A²) − 2 Re Tr(Q²). The two mixed traces vanish by the partial-trace pairing.

**Theorem 1.8 (Exact signed cold overlap).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_cold_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_cold_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every complex cold matrix Q and C = I ⊗ Q, Tr(C J_c C J_c†) = 2 Q₀₀ Q₁₁. The two spectator Z factors multiply to I.

**Theorem 1.9 (Exact cold cost on the lifted marginal).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_lift_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_lift_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian Q and K > 0, set δ = Re(Q₀₀ − Q₁₁). Then k(C) = k_* Re Tr(C²) − (K + q²/K) Re det Q + (K/2)(δ + q Re Tr(Q)/K)². The determinant includes the squared modulus of the complex off-diagonal entry.

**Theorem 1.10 (Cold lift bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_lift_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_lift_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Dropping the nonnegative square gives k(C) ≥ k_* Re Tr(C²) − (K + q²/K)d/4 with d = 4 Re det Q.

**Theorem 1.11 (Cold compression bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_compression_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_compression_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive semidefinite A and K > 0, the cold lift bound applies to Q = Tr_s(A)/2.

**Theorem 1.12 (Cold determinant from the eigenvalues).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.det_re_eq_eigenvalue_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.det_re_eq_eigenvalue_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian Q, Re det Q equals the product of its two real eigenvalues.

**Theorem 1.13 (Exact rank-two remainder purity).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_purity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_purity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian A with Re Tr(A) = a + b and Re Tr(A²) = a² + b², the identity is Re Tr(H²) = (a − b)²/2 + 4 Re det Q. The two moments give the rank-two formula and include the case b = 0.

**Theorem 1.14 (Realizing every feasible cold imbalance).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.exists_cold_matrix_imbalance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.exists_cold_matrix_imbalance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For ν ≥ μ ≥ 0, every δ in [−(ν − μ), ν − μ] is realized by a positive semidefinite Q with trace ν + μ and determinant νμ. Choose diagonal entries (ν + μ ± δ)/2 and both off-diagonal entries √((ν − μ)² − δ²)/2.

**Theorem 1.15 (Sharp cold cost with attainment).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For K > 0 and fixed cold eigenvalues ν ≥ μ ≥ 0, put t = −q(ν + μ)/K and δ = max(−(ν − μ), min(ν − μ, t)). The attained minimum over all positive semidefinite complex cold matrices with these eigenvalues is 2k_*(ν² + μ²) − (K + q²/K)νμ + (K/2)(δ − t)². The imbalance witness attains this value. The last term vanishes when t lies in the spectral interval, and the same formula applies when ν = μ.

**Theorem 1.16 (Exact splitting of the signed cold cost).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_split`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For arbitrary complex A, k(A) = k(C) + k(H). Multiplication by P₀ and conjugation by J_c or J_c† preserve the lifted cold algebra, so all mixed traces vanish.

**Theorem 1.17 (Complex remainder overlap on the actual cold jump).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.cold_overlap_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.cold_overlap_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian H, put X = Re Tr(H²P₀) and Y = Re Tr(H²P₁). These are the squared Hilbert–Schmidt norms of H J_c and H J_c†, respectively. Complex trace Cauchy–Schwarz gives |Re Tr(H J_c H J_c†)| ≤ √X √Y.

**Theorem 1.18 (Cold quadratic bound on the remainder).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_remainder_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_remainder_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For Hermitian H and K > 0, the signed overlap bound and a sum of two real squares give k(H) ≥ (k_* − K/4) Re Tr(H²).

**Theorem 1.19 (Range of the determinant correction).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_det_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_det_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

If A is positive semidefinite and Re Tr(A) = a + b, then 0 ≤ d ≤ (a² + b² − (a − b)²/2)/2.

**Theorem 1.20 (Moments in a complex orthonormal frame).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_frame_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_frame_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For U†U = I and a,b ≥ 0, A = U diag(0,0,b,a) U† is positive semidefinite and has ordinary moments Re Tr(A) = a + b and Re Tr(A²) = a² + b².

**Theorem 1.21 (Joint bound on the same matrix).**

Lean statement: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_joint_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_joint_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For positive semidefinite A with these moments, let ℓ = (a − b)²/2 and assume E_s ≥ Re Tr(H²). For K > 0, the signed cold cost then satisfies E_s + k(A) ≥ k_*(a² + b²) + (1 − K/4)ℓ + (1 − (2K + q²/K)/4)d.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldMarginal_liftCold`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldMarginal_posSemidef`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_compression_lower`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_lift_eq`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_lift_lower`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_minimum`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_remainder_lower`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.coldQuadratic_split`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.cold_overlap_le`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.cold_projectors`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.det_re_eq_eigenvalue_product`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.exists_cold_matrix_imbalance`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.liftCold_posSemidef`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.partialTrace_remainder`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_det_bounds`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_frame_moments`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_joint_lower`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.rankTwo_purity`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_cold_overlap`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_mul_liftCold`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuRankTwoSpectatorCompression.trace_remainder_sq`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker](WuTwoModeCliffordPluecker.md)
