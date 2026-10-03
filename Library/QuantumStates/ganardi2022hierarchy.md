---
bibkey: ganardi2022hierarchy
authors: Ray Ganardi; Marek Miller; Tomasz Paterek; Marek Żukowski
year: 2022
title: "Hierarchy of correlation quantifiers comparable to negativity"
doi: 10.22331/q-2022-02-16-654
url: https://arxiv.org/abs/2111.11887v2
claim: "For a bipartite state rho with partial transpose rho^{T_B} on the second system, the negativity is N(rho) = (||rho^{T_B}||_1 - 1)/2 and the partial transpose distance is d_T(rho, sigma) = ||rho^{T_B} - sigma^{T_B}||_1 / 2. Conjecture 1: for every density matrix rho, the infimum of d_T(rho, sigma) over the PPT states sigma equals N(rho)."
strata_touched:
  - D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation
license: citation-only
triage: anchor
---

# Hierarchy of correlation quantifiers comparable to negativity

Ray Ganardi, Marek Miller, Tomasz Paterek, Marek Żukowski, Quantum 6, 654
(2022); arXiv:2111.11887v2 (quant-ph). Quotations are from the arXiv v2
source, with its macros kept as printed (`\pt{\rho}` is $\rho^{T_B}$,
`\norm{A}` is $\|A\|_1$, `\dm` is the set of density matrices on
$\mathcal H_A\otimes\mathcal H_B$).

The partial transpose and the trace norm:

> Given a bipartite system $\hs_A \otimes \hs_B$, we denote partial transpose on the computational basis of $\hs_B$ as $T_B$.

> The trace norm of a matrix $A$ is defined as $\norm{A} = \Tr{\sqrt{A^\dagger A}}$.

The PPT states and the negativity:

> A state $\rho$ is PPT if $\pt{\rho} \geq 0$, and we denote the collection of such states as $\PPT$.

> The negativity of a state $\rho$ is defined as $N(\rho) = \half \left(\norm{\pt{\rho}} - 1\right)$.

The partial transpose distance (Definition):

> Let $\rho, \sigma \in \dm$ be two density matrices. The partial transpose distance $d_T(\rho, \sigma)$ is defined as \begin{align} d_T(\rho, \sigma) &= \half \norm{\pt{\rho} - \pt{\sigma}}. \end{align}

Conjecture 1:

> Let $\rho$ be a density matrix. Then \begin{align*} \inf_{\sigma \in \PPT} d_T(\rho, \sigma) &= N(\rho). \end{align*}

The paper proves the equality for states of positive binegativity,
$|\rho^{T_B}|^{T_B}\ge0$, and reports that $10^6$ random mixed states of two
qudits for each $d=2,\dots,6$ show no counterexample.

The encoding takes states on $\mathbb C^d\otimes\mathbb C^d$, indexes
matrices by `Fin d × Fin d`, transposes the second factor, and uses the
trace norm $\operatorname{Re}\operatorname{Tr}\sqrt{A^\dagger A}$; the
negativity and the distance are written in the claim exactly as defined
above.

## Verified locator

- DOI: https://doi.org/10.22331/q-2022-02-16-654 (Quantum 6, 654 (2022)).
- URL: https://arxiv.org/abs/2111.11887v2 (v2, 2022-02-09, the latest
  version; source `main.tex`, md5 `df386f803c4233dab0a6307e9c4dc578`): the
  partial transpose (l. 153), the trace norm (l. 155), the PPT states
  (l. 159), the negativity (l. 163), the partial transpose distance
  (l. 172–177), Conjecture 1 (l. 268–274) and the numerical evidence
  (l. 316–320).
