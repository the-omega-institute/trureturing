# Actual pure-qubit cost infimum

## Abstract

The full finite affine-readout pure-qubit cost infimum has quadratic coefficient one quarter of the weighted score-square projection residual.

Let Jm be Fin m. For positive probabilities p summing to one and a centered nonzero real direction v, define the scores, their second moment B, and their third moment M3 by

$s_j=\frac{v_j}{p_j},\quad B=\sum_{j\in J_m}p_js_j^2=\sum_{j\in J_m}\frac{v_j^2}{p_j},\quad M_3=\sum_{j\in J_m}p_js_j^3.$

The weighted squared residual after projecting the score square onto the span of the constant function and the score is

$V=\sum_{j\in J_m}p_j\left(s_j^2-B-\frac{M_3}{B}s_j\right)^2=\sum_{j\in J_m}p_js_j^4-B^2-\frac{M_3^2}{B}.$

Here costs and C2 are the attainable cost set and its guarded real infimum from ActualPureQubitGeometry, with the full IsProgram predicate there. BddBelow(S) means that S has a real lower bound. IsGLB(S,c) means that c is a lower bound and every real lower bound is at most c:

$\operatorname{BddBelow}(S)\ \Leftrightarrow\ \exists b\in\mathbb R,\forall q\in S,b\le q,\qquad\operatorname{IsGLB}(S,c)\ \Leftrightarrow\ (\forall q\in S,c\le q)\land(\forall b\in\mathbb R,(\forall q\in S,b\le q)\Rightarrow b\le c).$

All radii in the statement are real. The right limit is through every positive real radius tending to zero, and the three eventual properties hold together on one positive interval.

**Theorem 1.1 (Exact quadratic infimum coefficient).**

$$\begin{aligned}&\forall m\in\mathbb N,\ p,v:J_m\to\mathbb R,\\&(\forall j\in J_m,0<p_j)\land\sum_{j\in J_m}p_j=1\land\sum_{j\in J_m}v_j=0\land v\neq0\\&\land\ (\exists i,j,k\in J_m,\ s_i\neq s_j\land s_i\neq s_k\land s_j\neq s_k)\\&\longrightarrow\quad0<V\\&\land\ (\exists\delta>0,\forall R\in\mathbb R,\ 0<R<\delta\longrightarrow\\&\qquad\operatorname{costs}(p,v,R)\neq\emptyset\land\operatorname{BddBelow}(\operatorname{costs}(p,v,R))\land\operatorname{IsGLB}(\operatorname{costs}(p,v,R),C_2(p,v,R)))\\&\land\lim_{R\to0^+}\frac{C_2(p,v,R)-B}{R^2}=\frac V4\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite positive probability data, a nonzero centered direction, and at least three distinct scores, the residual is positive and the normalized infimum excess tends to one quarter of that residual as real positive radii tend to zero. Repeated and zero individual scores are allowed. Cubic approximate minimizers suffice; no optimum is assumed attained. This result makes no two-score attainment or unrestricted CPTP processor equivalence claim.

The lower bound uses the joint limit of feasible rank-two coefficients: positivity, normalization, and the spectral cost equation exclude a positive limiting transverse parameter when three scores are distinct. The remaining diagonal coefficients converge to the normalized weighted score squares. An exact matching inequality then gives the quadratic lower coefficient. The rank-one branch has a fixed positive cost gap, and a smooth family of actual programs supplies the matching upper bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitCostInfimum.result`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitFisherRank](ActualPureQubitFisherRank.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitUpperFamily](ActualPureQubitUpperFamily.md)
