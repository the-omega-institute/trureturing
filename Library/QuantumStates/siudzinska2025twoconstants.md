---
bibkey: siudzinska2025twoconstants
authors: Katarzyna Siudzińska
year: 2025
title: Measures from conical 2-designs depend only on two constants
doi: 10.1088/1751-8121/ae0203
url: https://arxiv.org/abs/2506.18211
claim: "The concurrence lower bound of a conical 2-design is eta times (the trace norm of its correlation operator minus xi), with eta = sqrt(2/(d(d-1)))/S and xi = C_max."
strata_touched:
  - D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1088/1751-8121/ae0203

Source: https://arxiv.org/abs/2506.18211

J. Phys. A: Math. Theor. 58 (2025) 375302. Section 2, Eq. (9),
PDF p. 2: the conical-design identity. Section 6, Eq. (59), PDF p. 9:
the measurement correlation operator. Section 7, “Concurrence lower bound”,
Theorem 6, Eqs. (73)–(74), PDF p. 10: the two-constant formula.
The DOI and title match the Crossref record.

# The two-constant concurrence formula

Section 2 states:

> By definition, $\mathcal{P}$ is a conical 2-design if
> $\sum_{\alpha=1}^N\sum_{k=1}^{M_\alpha}P_{\alpha,k}\otimes P_{\alpha,k}=\kappa_+I_d\otimes I_d+\kappa_-F_d$,
> where $\kappa_+\geq\kappa_->0$.

Section 6 defines the correlation operator in Eq. (59) and states:

> The elements of $\mathcal{B}(\rho)$ in the basis of $\omega_{\alpha,k}$ form the correlation matrix $\mathcal{B}_{\alpha,k;\beta,\ell}=\operatorname{Tr}[\rho(P_{\alpha,k}\otimes P_{\beta,\ell})]$.

Its matrix in that basis has entries $\operatorname{tr}[\rho(P_i\otimes P_j)]$.
Theorem 6 refers to Eq. (60); the defining operator expression is Eq. (59).
Section 7, Theorem 6 states:

> The concurrence of a mixed bipartite state $\rho$ is lower bounded by
> $\mathcal{N}_{\min}(\rho)=\eta\Big[\|\mathcal{B}(\rho)\|_{\tr}-\xi\Big]$,
> where $\mathcal{B}(\rho)$ is the correlation operator from eq. (60) and
> $\eta=\frac{1}{S}\sqrt{\frac{2}{d(d-1)}},\qquad \xi=\mathcal{C}_{\max}$.

With $\alpha=\kappa_+$, $\beta=\kappa_-$, $S=\beta$ and
$\mathcal{C}_{\max}=\alpha+\beta$, this is precisely
$B_E(\rho)=c_d(\|P_E(\rho)\|_1-\alpha-\beta)/\beta$.
The measurement labels are flattened to Fin m; there is no extra
normalization of the effects or of the correlation matrix. The comparison
uses this bound with the same design on both subsystems.
