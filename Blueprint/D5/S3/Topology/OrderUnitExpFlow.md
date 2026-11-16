# Zero contact and the original Banach exponential

## Abstract

Zero contact against the full continuous positive dual forces the actual exponential of a bounded real operator to preserve the same cone at every real time, in arbitrary Banach dimension.

**Theorem 1.1 (All real times preserve the same cone).**

$$\forall E \in Types,\; RealBanachSpace\left(E\right) \Rightarrow \left(\forall A \in ConeUnitData\left(E\right),\; \forall H \in ContinuousRealEndomorphisms\left(E\right),\; \left(\forall beta \in ContinuousRealDual\left(E\right),\; \left(\forall c \in E,\; ConeMember\left(A, c\right) \Rightarrow 0 \le beta\left(c\right)\right) \Rightarrow \left(\forall c \in E,\; ConeMember\left(A, c\right) \Rightarrow \left(beta\left(c\right) = 0 \Rightarrow beta\left(H\left(c\right)\right) = 0\right)\right)\right) \Rightarrow \left(\forall t \in R,\; \forall c \in E,\; ConeMember\left(A, c\right) \Rightarrow ConeMember\left(A, OperatorExp\left(smul\left(t, H\right)\right)\left(c\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitExpFlow.zero_contact_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Types denotes the type universe, R the real scalars, and RealBanachSpace(E) the original instances NormedAddCommGroup E, NormedSpace R E and CompleteSpace E. ConeUnitData(E) is exactly OrderUnitNorm.Data E: a convex cone C, unit u, zero in C, closedness of C, salience of C and u in the interior of C. ConeMember(A,c) means membership in this same C. ContinuousRealEndomorphisms(E) and ContinuousRealDual(E) use the given original norm, and OperatorExp is precisely NormedSpace.exp in its continuous endomorphism algebra.

The hypothesis ranges over every original continuous real linear beta nonnegative on C and every c in C. It requires beta(c)=0 to imply beta(Hc)=0. The conclusion quantifies every real t, including negative t, and every c in C. The zero carrier and zero functional remain included. No finite-dimensionality, normality, equality of the original norm with the order norm, uniform quasipositivity constant, or condition H(u)=0 is assumed.

For the forward implication it suffices that every positive zero contact has beta(Hc) nonnegative. Set a=orderNorm(Hu)+1 and d=a u-Hu. The frozen attained order-radius bound gives d-u in C. For 0<epsilon<1 use w(s)=(1-epsilon) exp(sH)y+epsilon exp(a s)u. At s=0 the pinned convex-combination interior theorem puts w(0) in the interior directly. The original operator exponential is differentiable because H is bounded and E is complete. Its derivative gives w'(s)=H(w(s))+epsilon exp(a s)d.

The private no_exit lemma proves a general differentiable-curve statement on the original normed carrier. If w first fails to be interior in a compact real time interval, the closed bad-time set has a least element T>0. Earlier times are interior, and closedness of C puts w(T) in C. The frozen boundary_support theorem supplies a continuous positive beta with beta(w(T))=0 and beta(u)>0. Left difference quotients are nonpositive, so beta(w'(T)) is at most zero. Cross-positivity and beta(d)>=beta(u)>0 make that same derivative strictly positive, a contradiction. Compactness is used only for the real time interval; the carrier need not be locally compact.

Consequently the perturbed orbit stays interior for every nonnegative time. At each fixed time epsilon tends to zero from above, and original closedness gives exp(tH)y in C. Zero contact gives cross-positivity for both H and -H. Apply the forward argument to -H at time -t for negative t; negation of the scalar and operator identifies the actual exponent exactly. The live new inference is the arbitrary-carrier first-exit argument and its original continuous-operator perturbation, rather than a call to the finite-dimensional cross_positive_flow theorem.

This proof extends the repository's finite-dimensional first-exit method to the original Banach topology. It reuses OrderUnitNorm.Data.boundary_support, norm_attained and pinned convex and exponential calculus. The private add_unit_interior theorem is not republished or reproved: the perturbed initial vector is instead the direct convex combination (1-epsilon)y+epsilon u. No literature originality is asserted.

For C128 (28.5), the intended substitution is H=delta_a on the same supplied complete carrier and actual cone. This result supplies only the zero-contact-to-cone-flow implication. Constructing that actual closed salient solid cone, the original positive-c square bound, transporting original q positivity and evaluations to all continuous positive functionals, proving the original delta_a zero-contact premise and D(a,u)=0, the Jordan automorphism and Leibniz bridge, bidual JBW extension, full associator rigidity and physical conclusions remain separate obligations. Unit preservation also requires a separate proof of H(u)=0.

## References

- Truth anchor: `D5/S3/Topology/OrderUnitExpFlow.zero_contact_exp`
- Dependency: [D5/S3/Topology/OrderUnitNorm](OrderUnitNorm.md)
