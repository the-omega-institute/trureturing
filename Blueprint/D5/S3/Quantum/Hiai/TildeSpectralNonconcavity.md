# TildeSpectralNonconcavity

## Abstract

Joint-concavity classification of the tilde spectral trace.

**Theorem 1.1 (Off-midpoint strict Jensen violations).**

$$\forall alpha, p: \mathbb{R},\ 0<alpha\land alpha<1\land 0<p\land alpha\neq\frac{1}{2}\implies\ \exists A, C, B: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}),\ \operatorname{PosDef}(A)\land \operatorname{PosDef}(C)\land \operatorname{PosDef}(B)\land \exists theta: \mathbb{R},\ 0<theta\land theta<1\land\ \operatorname{tildeTrace}(alpha, p, (1-theta)A+thetaC, B)<(1-theta)\operatorname{tildeTrace}(alpha, p, A, B)+theta\operatorname{tildeTrace}(alpha, p, C, B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/TildeSpectralNonconcavity.strict_first_variable_jensen_violation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For every 0 < alpha < 1, alpha different from one half, and p > 0, positive definite complex 2 by 2 matrices A, C and one common B violate first-variable concavity at a real weight theta in (0,1).

The base-first geometric mean is X^(1/2) (X^(-1/2) Y X^(-1/2))^alpha X^(1/2). Put K=A^(-p) #_alpha B^p. The actual functional is the real trace of (K^(1/2) A^(2p(1-alpha)) K^(1/2))^(1/p). Every matrix power is CFC.rpow. The same generic definition is used for every finite dimension.

Let r=1-alpha, gamma=(3/2)^r, eta=4^r, delta=(gamma-1)/(2(eta-gamma)), q=delta^(1/(2r-1)), and w=1/(1+q). The normalized rank-one projector has diagonal entries w and 1-w and off-diagonal entries sqrt(w(1-w)). For A_x=diag(x,1), set mu=1-w+w x^p and nu=1-w+w x^(2pr). Normalized rank-one compression gives K=mu^(-r) P and T(A_x,P)=(mu^(-r) nu)^(1/p). The existing two_point_cfc supplier evaluates the actual matrix powers.

With a=q^(1/p), b=(2q)^(1/p), the exact difference of the scalar cores is (1-w)^alpha (gamma-1)/(2 3^r)>0. This works for both signs of 2r-1. Set theta=(h(a)-h(b))/(2h(a)) and c=a+(b-a)/theta. Then b=(1-theta)a+theta c and positivity of h(c) gives a strict Jensen gap. Continuity of positive matrix powers at the three fixed SPD first inputs preserves that gap for one common SPD B=P+epsilon I. No negative power is applied to the singular projector.

**Theorem 1.2 (All-dimension SPD classification).**

$$\forall alpha, p: \mathbb{R},\ 0<alpha\land alpha<1\land 0<p\implies\ ((\forall n: \mathbb{N}, \operatorname{JointlyConcaveOn}(\operatorname{SPD}(\operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C})), \operatorname{SPD}(\operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{C})), \operatorname{tildeTrace}(alpha, p))) \iff (alpha=\frac{1}{2}\land p\le1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/TildeSpectralNonconcavity.joint_concavity_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

Under 0 < alpha < 1 and p > 0, joint concavity on SPD complex matrix pairs simultaneously in every Fin n dimension is equivalent to alpha=1/2 and p<=1. The necessary direction uses strict Fin2 SPD witnesses; the equivalence is not asserted separately for each dimension.

At alpha=1/2 put C=A^(p/2) B^p A^(p/2) and L=A^(-p)#_(1/2)B^p. The actual Riccati identity A^(p/2)L A^(p/2)=C^(1/2) and equal Gram spectral traces prove T=ReTr(C^(1/(2p))). Every power is CFC.rpow.

At theta=0 the existing PsiMeanTraceConcavity.psi_jointly_concave supplies fixed-congruence Epstein concavity for 0<p<=1. The existing Gram and Holder/Young suppliers give F_p(A,B)<=(E_A(Z)+E_B((Z^(-1))*))/2 for every invertible Z. The optimizer Z=A^(-p/2)C^(1/4) attains equality. Selecting it at the mixed SPD pair and applying the fixed-Z inequalities proves generic joint concavity.

For p>1 the positive-power Gram functional has endpoint values 2^(-1/(2p)) at (Q,P) and (I-Q,P), and middle value 2^(-1/2) at (I/2,P), where Q=diag(1,0) and P is the balanced rank-one projector. Positive-power continuity preserves the strict gap for A0=diag(1-s,s), A1=diag(s,1-s), and B=(1-s)P+s(I-P), with common s in (0,1/2). The actual TILDE identity is used only at the SPD inputs. The middle Gram value is 2^(-1/2)(sqrt(1-s)+sqrt(s)).

Midpoint sufficiency is classical, including Zhang1811.01205v2. The retained content is the consumed formal assembly into the actual functional classification and the all-off-midpoint witnesses. Supported-PSD extensions, UNTILDE and Problem 5.18 are separate obligations. Source comparisons are bounded to inspected manuscripts and the pinned repository suppliers.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/TildeSpectralNonconcavity.joint_concavity_classification`
- Truth anchor: `D5/S3/Quantum/Hiai/TildeSpectralNonconcavity.strict_first_variable_jensen_violation`
- Dependency: [D5/S3/Quantum/Hiai/PsiMeanTraceConcavity](PsiMeanTraceConcavity.md)
- Dependency: [D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus](../Matrix/TwoPointFunctionalCalculus.md)
