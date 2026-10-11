---
bibkey: bunthpitriktitkosvirosztek2024wasserstein
authors: G. Bunth; J. Pitrik; T. Titkos; D. Virosztek
year: 2024
title: "On the metric property of quantum Wasserstein divergences"
doi: 10.1103/PhysRevA.110.022211
url: https://arxiv.org/abs/2402.13150v4
claim: "Section 4.1 Proposition 3, equation (35), states D²(ρ,ρ)=4(1−√(1−|bρ|²)), corresponding for eigenvalues (1±r)/2 to 8−4(tr√ρ)²; Section 5.1 defines the Wasserstein complexity and states that its convexity is open."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings
  - D5/S3/Quantum/QuantumChannels/WassersteinComplexityNonconvex
license: citation-only
triage: anchor
---

# Quantum Wasserstein divergences and channel complexity

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.110.022211

Source: https://arxiv.org/abs/2402.13150v4

## Source statements

The paper defines couplings by prescribed partial traces, the quadratic quantum Wasserstein distance in equation (eq:2-Wass-quant-def), and the divergence $d_{\mathcal A}$ in equation (eq:mod-qw-dist-def). Section 5.1 (PDF p. 17) defines the Wasserstein complexity by

> Given a finite collections of observables $\mathcal A=\{A_1, \dots, A_k\}$, let us define the Wasserstein complexity of a channel $\Phi:\mathcal S(\mathcal H)\rightarrow\mathcal S(\mathcal H)$ by $C_{W}(\Phi):=\max_{\rho\in\mathcal S(\mathcal H)} d_{\mathcal A}(\rho, \Phi(\rho))$.

The same section (PDF p. 18) states:

> We note that whether the Wasserstein complexity (37) is convex or not is an open question.

The self-cost identity used by the qubit settlement is literature-attested by Section 4.1, Proposition 3, equation (35): $D^2(\rho,\rho)=4(1-\sqrt{1-|b_\rho|^2})$, which becomes $8-4(\operatorname{tr}\sqrt\rho)^2$ for eigenvalues $(1\pm r)/2$.

The Lean modules use the preregistered finite-dimensional qubit conventions and refute the convexity question for the Pauli triple by an explicit midpoint.

## Definitions and encoding

Section 1.2 defines the coupling set by

$$
\mathcal C(\rho,\omega)=\{\Pi\in\mathcal S(\mathcal H\otimes\mathcal H^*)\mid
\operatorname{tr}_{\mathcal H^*}\Pi=\omega,\quad
\operatorname{tr}_{\mathcal H}\Pi=\rho^T\}.
$$

Equation (eq:2-Wass-quant-def) is

$$
D_{\mathcal A}^{2}(\rho,\omega)=\inf_{\Pi\in\mathcal C(\rho,\omega)}
\sum_{j=1}^{k}\operatorname{tr}[(A_j\otimes I-I\otimes A_j^T)\Pi(A_j\otimes I-I\otimes A_j^T)].
$$

Equation (eq:mod-qw-dist-def) is

$$
d_{\mathcal A}(\rho,\omega)=\sqrt{D_{\mathcal A}^{2}(\rho,\omega)
-\tfrac12(D_{\mathcal A}^{2}(\rho,\rho)+D_{\mathcal A}^{2}(\omega,\omega))}.
$$

The finite-dimensional encoding uses complex matrices on `Fin d`; the coupling matrix is indexed by `Fin d × Fin d`. Its positive semidefinite, trace-one condition is stated on that product index type. This is a Lean elaboration repair preserving the source state condition on the tensor product. The dual factor uses `Matrix.transpose`. The frozen `partialTraceRight` and `partialTraceLeft` are the literal explicit sums, and the frozen `IsDensity` is the literal positive semidefinite, trace-one condition. `CW` uses the supremum of the source maximum's value set. Its boundedness and the existence of admissible couplings are proved in the supporting module. The universal claim retains the literal zero-dimensional case.

## Scope of the refutation

The repository construction uses the Pauli triple and dephasing parameter $t=1/4$. The unitary endpoint channels are mixed with weight $s=1/2$. The midpoint complexity is at least $\sqrt{1+\sqrt3}$, while both endpoints have complexity at most $\sqrt2$. The supporting module proves the exact self-cost formula for every qubit density state. No assumption of the source's previously proved metric statements is changed by this refutation. The same midpoint exceeds both endpoint complexities, so quasi-convexity also fails. All three channels are unital, so restriction to unital channels does not restore convexity. The exact value of the complexity for the dephasing family remains open.

## Counterexample family

The following extension is proved in prose; the Lean settlement specializes it to $t=1/4$. For $0<t<1/2$, set $U_\pm=\sqrt{1-t}\,I\pm i\sqrt t\,Z$ and $\Phi_\pm=\operatorname{Ad}(U_\pm)$. Their midpoint is the unital channel $\Psi_t=(1-t)\operatorname{id}+t\operatorname{Ad}(Z)$.

For a qubit state $\rho$, put $S=\sqrt\rho$. The vectorized $U_\pm S$ coupling has cross cost $8-4|\operatorname{tr}(U_\pm S)|^2$. Since $S$ is positive, its diagonal entries are real, so $|\operatorname{tr}(U_\pm S)|^2\ge(1-t)(\operatorname{tr}S)^2$. Unitary covariance preserves the self cost, giving $d_{\mathcal A}(\rho,\Phi_\pm(\rho))^2\le4t(\operatorname{tr}S)^2\le8t$.

At $\rho=|+\rangle\langle+|$, the pure marginal fixes the midpoint cross cost at $4+4t$. The input self cost is $4$ and the output self cost is $4-8\sqrt{t(1-t)}$. Consequently,

$$
C_W(\Psi_t)^2\ge4t+4\sqrt{t(1-t)}>8t\ge C_W(\Phi_\pm)^2.
$$

The strict inequality follows from $t(1-t)>t^2$. Thus subtracting the output self cost causes the convexity failure: channel mixing lowers that self cost while raising the cross cost. The same family refutes quasi-convexity among unital channels.

The pinned numerical check, rerun by the implementation seat, gives: `python3 check.py`, exit `0`, `bad= 0`. The experiment entry is `docs/reports/bunth-pitrik-titkos-virosztek-2024-wasserstein-complexity-convexity/check.py` in `the-omega-institute/trureturing-experiments` at commit `10a541e9aacff47302154c721e10ff180fda60aa`, SHA-256 `04787a6acc2c5bccda908bcb90ffd00d928e418e14cebc28bfa5f2d90f9c68db`.
