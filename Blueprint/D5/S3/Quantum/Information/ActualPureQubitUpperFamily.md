# Actual pure-qubit upper family

## Abstract

Normalized positive effect matrices and pure-state arcs give a matching upper family.

J is an arbitrary finite outcome index set and Jm is Fin m. All scalars and radius parameters are real. PSD means positive semidefinite, the qubit identity is the two-by-two identity matrix, and P(R) denotes the set of subsets of the real line. The following moment notation is used with the outcome set of each statement; eR is shorthand after the function t has been chosen.

$\mu_3=\sum_j\frac{d_j^3}{p_j^2},\quad\mu_4=\sum_j\frac{d_j^4}{p_j^3},\quad\alpha=-2\mu_3,\quad e_R=t(R)^2$

root, effect, radiusMap, extendedCost and IsProgram are exactly the functions and full program predicate in ActualPureQubitGeometry. In particular IsProgram includes the canonical density-state realization, positive exact complex Born probabilities, and equality to the spectral cost at zero. The vector written as the square root of B times d is the function taking j to that scalar multiple of d at j. Both limits below are through all positive real radii tending to zero.

**Theorem 1.1 (Normalized positive effect family).**

$$\begin{aligned}&\forall J\ \mathrm{finite},\ p,d:J\to\mathbb R,\ B\in\mathbb R,\\&(\forall j\in J,0<p_j)\land\sum_{j\in J}p_j=1\land\sum_{j\in J}d_j=0\land\sum_{j\in J}\frac{d_j^2}{p_j}=1\land0<B\\&\longrightarrow\exists w,t:\mathbb R\to\mathbb R,\ w(0)=1\land t(0)=0\\&\land\lim_{R\to0^+}\frac{\operatorname{extendedCost}(B,\alpha,w)(t(R)^2)-B}{R^2}=\frac{B^2}{4}(\mu_4-1-\mu_3^2)\\&\land\exists\delta>0,\forall R\in\mathbb R,\ 0<R<\delta\longrightarrow\\&(0<R\land0<t(R)\land t(R)<1\land0<w(e_R)\\&\land\sum_{j\in J}\operatorname{root}(p_j,d_j,\alpha,e_R,w(e_R))=1\\&\land\ (\forall j\in J,\operatorname{PSD}(\operatorname{effect}(p_j,d_j,\alpha,e_R,w(e_R))))\\&\land\sum_{j\in J}\operatorname{effect}(p_j,d_j,\alpha,e_R,w(e_R))=1_2\land\operatorname{radiusMap}(B,\alpha,w)(t(R))=R\\&\land\ (\forall j\in J,\ 0<p_j-\alpha e_Rw(e_R)d_j\land0<(p_j-\alpha e_Rw(e_R)d_j)^2-4e_R(1-e_R)w(e_R)^2d_j^2)\\&\land\ (\forall j\in J,\ R(1+t(R))|\sqrt Bd_j|<p_j))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_effect_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same functions w and t satisfy the initial values, the moment limit, normalization of the small roots and effects, the radius equation, and every strict margin in the displayed conjunction.

**Theorem 1.2 (Matching family of actual programs).**

$$\begin{aligned}&\forall m\in\mathbb N,\ p,d:J_m\to\mathbb R,\ B\in\mathbb R,\\&(\forall j\in J_m,0<p_j)\land\sum_{j\in J_m}p_j=1\land\sum_{j\in J_m}d_j=0\land\sum_{j\in J_m}\frac{d_j^2}{p_j}=1\land0<B\\&\longrightarrow\exists N:\mathbb R\to(J_m\to\mathbb C^{2\times2}),\ \rho:\mathbb R\to(\mathbb R\to\mathbb C^{2\times2}),\ I:\mathbb R\to\mathcal P(\mathbb R),\ Q:\mathbb R\to\mathbb R,\\&\lim_{R\to0^+}\frac{Q(R)-B}{R^2}=\frac{B^2}{4}(\mu_4-1-\mu_3^2)\\&\land\ (\exists\delta>0,\forall R\in\mathbb R,\ 0<R<\delta\longrightarrow\operatorname{IsProgram}(p,\sqrt Bd,R,N(R),\rho(R),I(R),Q(R)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_upper_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The functions N, rho, I and Q give actual programs simultaneously for every sufficiently small positive radius, with direction equal to the square root of B times d and the displayed cost limit.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_effect_family`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitUpperFamily.actual_upper_family`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](ActualPureQubitGeometry.md)
