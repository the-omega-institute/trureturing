# The spectral geometric Renyi comparison has a necessary boundary

## Abstract

The spectral geometric Renyi comparison fails above its sharp parameter boundary.

Section 2 defines the weighted geometric mean A#_alpha B = A^(1/2)(A^(-1/2) B A^(-1/2))^alpha A^(1/2), with # = #_(1/2), and the spectral geometric mean SG_(alpha,p) = F_alpha(A^p,B^p)^(1/p), where F_alpha(A,B) = (A^(-1)#B)^alpha A (A^(-1)#B)^alpha. These objects and their real continuous functional calculus powers are reused from their existing declarations.

Problem 3.5 states: "When α>1, no necessary condition on p,q>0 for SG_{α,p} ≺log R_{α,q} to hold is known." It continues: "This suggests us that SG_{α,p} ≺log R_{α,q} might hold for any p,q>0." Theorem 3.4(1) proves the comparison for p at most alpha q. The largest eigenvalue inequality in dimension two is already necessary for the proposed universal comparison.

**Definition 1.1 (The spectral geometric mean).**

Lean statement: `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.SG`

*Formalization.* `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.SG` (`✓ std3`).

*Citation.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The reused definition SG_(alpha,p)(A,B) applies F_alpha to A^p and B^p and then takes the one over p power, where F_alpha(X,Y) = (X^(-1)#Y)^alpha X (X^(-1)#Y)^alpha. The weighted geometric mean and the spectral real matrix power mpow are the existing definitions. The comparison is restricted to positive definite complex inputs and positive p.

**Definition 1.2 (The Renyi mean).**

Lean statement: `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiRMean`

*Formalization.* `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiRMean` (`✓ std3`).

*Citation.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For positive definite complex matrices, real alpha and positive q, R_(alpha,q)(A,B) is the one over q power of A^((1-alpha)q/2) B^(alpha q) A^((1-alpha)q/2). The reused definition hiaiRMean uses CFC.rpow for every real matrix power. The expression agrees with the source spectral definition on the positive definite domain.

**Definition 1.3 (The universal largest eigenvalue assertion).**

Lean statement: `D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.claim`

*Formalization.* `D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.claim` (`✓ std3`).

*Citation.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The closed assertion quantifies over every real alpha greater than one, every positive p and q, and every pair of positive definite complex two by two matrices. For every Hermitian witness for each mean, it requires the largest eigenvalue of SG_(alpha,p) to be at most the largest eigenvalue of R_(alpha,q). Both means are Hermitian on these positive definite inputs. This is the first log-majorization inequality in Problem 3.5, restricted to a dimension included in the source universal comparison.

**Theorem 1.4 (The proposed unrestricted comparison is false).**

Lean statement: `D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.result` (`✓ std3`). ∎

*Resolves.* `Problems/hiai-2026-problem-3-5-spectral-geometric-renyi` (refuted) by `D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hiai-2026-problem-3-5-spectral-geometric-renyi","declaration_gid":"D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The conclusion is the negation of the closed assertion. The counterexample construction fixes alpha greater than one, positive q, and p greater than alpha q. Put k=alpha q/p and choose u positive with p sinh(k(alpha-1)u) less than q sinh((alpha-1)u). Write D(w)=diag(exp(w),exp(-w)) and let J_theta have entries [-cos(2 theta),sin(2 theta);sin(2 theta),cos(2 theta)]. This is a real symmetric involution. Set T_theta=cosh(u/2)I+sinh(u/2)J_theta, X=D(alpha u), Y_theta=T_theta X T_theta, A=D(alpha u/p), and B_theta=Y_theta^(1/p). The matrices are positive definite. The determinant-one facts for the inputs and outputs are paper calculations (det A = det B = 1), not formalized; failure of the log-majorization follows directly from the first largest-eigenvalue product inequality. Uniqueness of the positive Riccati solution identifies X^(-1)#Y_theta=T_theta, and two-point functional calculus computes its alpha power. Both output cores equal the identity at zero angle. Their off-diagonal derivatives are d_S=2 sinh(alpha u) and d_R=2(sinh(alpha u)-sinh((alpha-1)u)) sinh(k(alpha-1)u)/sinh((alpha-1)u). The explicit two by two largest eigenvalue formula gives right-hand output slopes d_S/p and d_R/q. The choice of u makes the former strictly larger, so a sufficiently small positive angle gives the strict largest eigenvalue violation. In particular alpha=2, q=1, p=3 refutes the universal assertion. The source sufficiency for p at most alpha q and the paper extension by a common identity block give the sharp range in each dimension at least two. The sufficient comparison, the direct sum extension, the alternative fixed-spectrum rotation family, and the source Theorem 3.3 for alpha strictly between zero and one are not additional Lean conclusions here.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.result`
- Truth anchor: `D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement.hiaiRMean`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.SG`
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](AlternativeMeanLinearization.md)
- Dependency: [D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic](HiaiHarmonicArithmetic.md)
- Dependency: [D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement](SharpWeightedLin/Settlement.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation](SpectralGeometricLogEuclideanRefutation.md)
