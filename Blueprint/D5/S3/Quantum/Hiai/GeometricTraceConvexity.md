# GeometricTraceConvexity

## Abstract

Joint convexity of Hiai's original geometric trace on positive definite matrices.

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

The definition is Hiai (2.1)/(2.2), page 4 of arXiv:2510.04691v3; Problem 5.18 is on page 33. Classical Hiai, Carlen-Lieb, Zhang and the attributed Physlib suppliers retain their source credit. This is a connected formal assembly on SPD, with no novelty claim for reused theorems. It covers the original open parameter rectangle on SPD and known parameter endpoints; it does not complete the full support-sensitive PSD original domain.

The remaining original obligations are PSD support inclusion s(A)>=s(B), generalized inverse zero on kernels, the same epsilon I added to ORIGINAL A and B before their p-powers, a norm/trace limit, and support-domain convexity. Compression transport and block-support identities are not asserted. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration or official acceptance is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/GeometricTraceConvexity.geometric_trace_jointly_convex`
- Dependency: [D5/S3/Quantum/Hiai/CarlenLiebConvexity](CarlenLiebConvexity.md)
- Dependency: [D5/S3/Quantum/Hiai/InverseGeometricIdentification](InverseGeometricIdentification.md)
