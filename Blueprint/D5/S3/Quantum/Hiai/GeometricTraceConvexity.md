# GeometricTraceConvexity

## Abstract

Joint convexity of Hiai's original CFC geometric trace on supported PSD pairs.

**Theorem 1.1 (The boundary-inclusive SPD rectangle).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ alpha, p: \mathbb{R},\ 1\le alpha \le 2\land \frac{1}{2}\le p \le 1\implies\ \operatorname{JointlyConvexOn}(\operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \Lambda A, B\mapsto\operatorname{tracePower}(\frac{1}{p}, \operatorname{geometricMean}(alpha, \operatorname{rpow}(A, p), \operatorname{rpow}(B, p))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/GeometricTraceConvexity.geometric_trace_jointly_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For every finite complex matrix index type d with DecidableEq, including empty d, and every 1 <= alpha <= 2 and 1/2 <= p <= 1, the function F(A,B)=Re Tr((A to exponent p geometricMean at weight alpha B to exponent p) to exponent 1/p) is jointly convex on the two positive definite cones. The base is A to exponent p, the FIRST matrix argument. All powers are actual CFC spectral powers. A and B need not commute.

Set theta=alpha-1, r=1/p, X=B to exponent p and M=geometricMean theta (B to exponent p) (A to exponent p). The existing all-real weighted symmetry and inverse sandwich identify the original mean with X inverse(M) X. Public matrix unit-congruence positivity and spectral strictness make M positive definite. Matrix nonsingular inverse agrees with Ring.inverse. The existing inverse variational theorem gives the invertible optimizer inverse(M) X, not necessarily selfadjoint, with equality and an upper bound for EVERY Z.

Since (B to exponent p) squared equals B to exponent 2p, the objective is 2 C_Z(B)-Psi_Z(A,B), where C_Z(B)=Re Tr((Z adjoint B to exponent 2p Z) to exponent 1/(2p)). The existing Carlen-Lieb fixed-congruence theorem at a=2p makes C_Z convex; its first component also supplies SPD domain convexity. The existing Hiai Psi theorem makes Psi_Z jointly concave for this same fixed invertible Z.

Choose ONLY the attained optimizer Zm at the mixed pair ((1-t)A0+tA1,(1-t)B0+tB1). Fixed-Zm objective convexity bounds F at this pair by the mixed endpoint objectives. Apply the universal variational upper bound at BOTH endpoints to that SAME Zm. Nonnegative weights then give joint convexity. No mixing of optimizers, uniqueness, compactness, assumed supremum attainment, A/B commutation, product positivity, or CFC transport through arbitrary congruence is used.

The definition is Hiai (2.1)/(2.2), page 4 of arXiv:2510.04691v3; Problem 5.18 is on page 33. Classical Hiai, Carlen-Lieb, Zhang and the attributed Physlib suppliers retain their source credit. This is a connected formal assembly on SPD, with no novelty claim for reused theorems. It supplies the regularized original parameter rectangle on SPD and known parameter endpoints for the extension to the full support-sensitive PSD original domain below.

The PSD endpoint below uses the same epsilon I added to both original matrices before their p-powers, the actual support spectral identity, and a trace limit.

**Theorem 1.2 (The original PSD support domain).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ alpha, p: \mathbb{R},\ 1\le alpha \le 2\land \frac{1}{2}\le p \le 1\implies\ \operatorname{ConvexOn}(\mathbb{R}, \operatorname{supportPairDomain}(d), \Lambda z\mapsto\operatorname{geometricTrace}(alpha, p, \operatorname{fst}(z), \operatorname{snd}(z)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/GeometricTraceConvexity.geometric_trace_support_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For every finite complex carrier d, including the empty carrier, supportPairDomain consists exactly of pairs (A,B) with A and B positive semidefinite and ker A contained in ker B. The unchanged geometricTrace formula is ConvexOn over this coupled set of pairs for 1 <= alpha <= 2 and 1/2 <= p <= 1. The mean is the classical base-first quasi-geometric mean G of Hiai, with A to exponent p as its base. It is distinct from SG and tilde-SG.

Fix a supported pair. Q=I-spectralSupport(A) is the kernel projection, and both A Q and B Q vanish. Finite-spectrum CFC gives the exact decomposition of (A+epsilon I) to exponent -p/2 into a support-restricted factor and epsilon to exponent -p/2 times Q. The inner sandwich is the supported sandwich plus Q, because the powered B regularization acts on Q as epsilon to exponent p. These use the actual curves (A+epsilon I) to exponent p and (B+epsilon I) to exponent p.

The support-restricted negative powers converge on the fixed finite spectrum. Positive powers are continuous on PSD matrices. At the limit, finite spectral intertwining removes Q between the outer A to exponent p/2 factors. The resulting mean is exactly the original Moore-Penrose CFC formula, including A=B=0 and empty carriers. Positive 1/p power continuity and trace continuity give the required real trace limit.

For an interior mixture, vanishing of a PSD quadratic form forces both endpoint A matrices to annihilate the vector. Their kernel inclusions then give annihilation by the mixed B. The t=0 and t=1 cases are separate. Adding the same epsilon I commutes exactly with mixing; apply the preserved SPD convexity theorem and pass the three trace limits through closed real order.

The limit concerns simultaneous additive epsilon I regularization of a fixed supported pair. It asserts no continuity on the entire support domain and uses no singular ring inverse or reverse-base identity. The exact original-domain endpoint is the formal target of Hiai Problem 5.18.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/GeometricTraceConvexity.geometric_trace_jointly_convex`
- Truth anchor: `D5/S3/Quantum/Hiai/GeometricTraceConvexity.geometric_trace_support_convex`
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation](../Entanglement/PrecessionUniversalThresholdRefutation.md)
- Dependency: [D5/S3/Quantum/Hiai/CarlenLiebConvexity](CarlenLiebConvexity.md)
- Dependency: [D5/S3/Quantum/Hiai/InverseGeometricIdentification](InverseGeometricIdentification.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](../Recovery/SpectralTransposeRecovery.md)
