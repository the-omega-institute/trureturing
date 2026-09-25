# Fisher information and the qubit rank alternative

## Abstract

Spectral SLD information bounds measurement Fisher information and controls the rank-one branch.

The first statement allows arbitrary finite matrix and outcome index sets n and J, including empty sets; Jm in the second is Fin m. PSD means positive semidefinite, 1n is the identity matrix, and all derivatives are real derivatives. C1(I) means continuously differentiable on I. spectralQFI is the spectral SLD information defined in ActualPureQubitGeometry; the displayed cost uses positivity at zero supplied by the hypotheses. The real rank is the dimension of the range of the real linear map effectReadout. Open refers to the ordinary topology of the real line.

**Theorem 1.1 (Measurement Fisher lower bound).**

$$\begin{aligned}&\forall n,J\ \mathrm{finite},\ N:J\to\mathbb C^{n\times n},\ \rho:\mathbb R\to\mathbb C^{n\times n},\ p,v:J\to\mathbb R,\\&(\forall j\in J,\operatorname{PSD}(N_j))\land\sum_{j\in J}N_j=1_n\land(\forall j\in J,0<p_j)\land\operatorname{DifferentiableAt}(\rho,0)\\&\land\ (\exists\delta>0,\forall u\in\mathbb R,\ |u|<\delta\longrightarrow\operatorname{PSD}(\rho(u)))\\&\land\ (\exists\delta_2>0,\forall u\in\mathbb R,\ |u|<\delta_2\longrightarrow\forall j\in J,\operatorname{Re}\operatorname{tr}(N_j\rho(u))=p_j+uv_j)\\&\longrightarrow\sum_{j\in J}\frac{v_j^2}{p_j}\le\operatorname{spectralQFI}(\rho(0),\rho'(0))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_fisher` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two neighborhood hypotheses are two-sided at zero. The lower bound applies to the spectral information of the differentiable positive curve with the stated exact real-part readout.

**Theorem 1.2 (Rank alternative and binary cost gap).**

$$\begin{aligned}&\forall m\in\mathbb N,\ N:J_m\to\mathbb C^{2\times2},\ \rho:\mathbb R\to\mathbb C^{2\times2},\ p,v:J_m\to\mathbb R,\ I\subseteq\mathbb R,\ \ell,h\in J_m,\\&\operatorname{Open}(I)\land0\in I\land v\neq0\land(\forall j\in J_m,0<p_j)\land(\forall j\in J_m,\operatorname{PSD}(N_j))\land\rho\in C^1(I)\\&\land\ (\forall u\in I,\operatorname{PSD}(\rho(u))\land\operatorname{tr}(\rho(u))=1\land\rho(u)^2=\rho(u))\\&\land\ (\forall u\in I,\forall j\in J_m,\operatorname{Re}\operatorname{tr}(N_j\rho(u))=p_j+uv_j)\land\frac{v_\ell}{p_\ell}<0\land0<\frac{v_h}{p_h}\\&\longrightarrow\operatorname{rank}_{\mathbb R}(\operatorname{effectReadout}(N))=2\ \lor\ -\frac{v_\ell}{p_\ell}\frac{v_h}{p_h}\le\operatorname{spectralQFI}(\rho(0),\rho'(0))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_rank_alternative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every chosen negative-score index and positive-score index, the conclusion is the displayed disjunction. The hypotheses require positive effects but do not require their sum to be the identity or I to be preconnected.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_fisher`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_rank_alternative`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](ActualPureQubitGeometry.md)
