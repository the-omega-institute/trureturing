---
bibkey: gourwallach2010fourqubits
authors: Gilad Gour; Nolan R. Wallach
year: 2010
title: "All Maximally Entangled Four Qubits States"
doi: 10.1063/1.3511477
url: https://arxiv.org/abs/1006.0036v2
claim: "Four-qubit marginal entropy: the Higuchi–Sudbery candidate, its known restrictions, and the unrestricted maximum question."
strata_touched:
  - D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1063/1.3511477

Source: https://arxiv.org/abs/1006.0036v2

# All Maximally Entangled Four Qubits States

## Purity and entropy boundaries

The discussion before Theorem 5:

> Hence, since $\tau_1$ is bounded by $1$, it follows that $\tau_2\leq 4/3<3/2$. That is, there are no 4-qubit states for which all the 3 reduced density matrices, obtained by tracing out two qubits, are proportional to the identity.

With the paper's tangle normalization, $\tau_2\leq4/3$ is the bound $\sum_{c}\operatorname{Tr}\rho_c^2\geq1$ over the three inequivalent two-versus-two cuts.

Theorem 10(a), p. 8, has the hypothesis $\psi\in\mathcal A$:

$$E_2^{(\alpha)}(\psi)\leq E_2^{(\alpha)}(|M\rangle)\quad\text{for }0<\alpha<2.$$

> with equality if and only if up to local unitaries $\psi=|M\rangle$.

Theorem 12, p. 9:

> Let $\psi\in\mathcal H_4$ and $\alpha\geq2$. Then,

$$E_2^{(\alpha)}(\psi)\leq5/3,$$

> with equality if and only if, up to local unitaries, $\psi$ is one of the cluster states given in Eqs.(3,4,5).

Theorem 12 concerns average Rényi entropy. Theorem 10's restricted-family conclusion does not provide the unrestricted von Neumann bound, and the cluster-state result for $\alpha\geq2$ does not settle the analogous unrestricted question for $1<\alpha<2$.
