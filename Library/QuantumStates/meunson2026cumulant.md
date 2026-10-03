---
bibkey: meunson2026cumulant
authors: A. Meunson; T. Deesuwan
year: 2026
title: "Cumulant-based quantum relative Rényi functional"
doi: 10.48550/arXiv.2606.31205
url: https://arxiv.org/abs/2606.31205v1
claim: "Conjecture 15 asserts that Q = -S_0^Q decreases under commutativity-preserving channels for noncommuting regularized states with output support inclusion."
strata_touched:
  - D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation
license: citation-only
triage: anchor
---

# Cumulant-based quantum relative Rényi functional

A. Meunson and T. Deesuwan, arXiv:2606.31205v1 (2026-06-30), quant-ph.
The source is Section VIII.A, PDF p. 18, Conjecture 15; regularization is
Eq. `state_regularized` and the relative Rényi functional is Eq. `regularized_Cu-Q`.

The source sentences and formulas are quoted verbatim below, including the stray
right parenthesis after sigma in Conjecture 15.

> Given $\rho,\sigma\in\mathcal D(\mathcal H)$ and a parameter $\varepsilon\in(0,1)$, define $\rho_\varepsilon := (1-\varepsilon)\rho + \varepsilon\frac{\mathbb{I}}{d}, \quad \sigma_\varepsilon := (1-\varepsilon)\sigma + \varepsilon\frac{\mathbb{I}}{d}$, where $d=\dim(\mathcal H)$.

> $S^{Q}_{\alpha}(\rho_\varepsilon\|\sigma_\varepsilon) := \frac{1}{\alpha-1} \ln \operatorname{Tr} \!\left[ \rho_\varepsilon e^{(\alpha-1) (\ln\rho_\varepsilon-\ln\sigma_\varepsilon)} \right]$

> Define $Q(\rho_\varepsilon\|\sigma_\varepsilon) := -S_0^Q(\rho_\varepsilon\|\sigma_\varepsilon)$.

> Let $\mathcal{H}$ be a finite-dimensional Hilbert space. A CPTP map $\mathcal{N}:\mathcal{B}(\mathcal{H})\to\mathcal{B}(\mathcal{H})$ is called a CoP channel if, for every pair $(\rho,\sigma)\in\mathcal{D}(\mathcal{H})\times \mathcal{D}(\mathcal{H})$ satisfying $[\rho,\sigma]=0$, one has $[\mathcal {N}(\rho),\mathcal {N}(\sigma)]=0$.

> \begin{conjecture}[QDPI at $\alpha=0$ for non-commuting inputs under CoP channels] Let $\rho,\sigma)\in \mathcal D(\mathcal H)\times\mathcal D(\mathcal H)$ satisfy $[\rho,\sigma]\neq0,$ where $\rho_\varepsilon,\sigma_\varepsilon$ are the regularized states defined in Eq.\eqref{state_regularized}. Suppose that $\mathcal N $ is a CoP channel satisfying $\operatorname{supp}\!\bigl(\mathcal N(\rho_\varepsilon)\bigr) \subseteq\operatorname{supp}\!\bigl(\mathcal N(\sigma_\varepsilon)\bigr). $ Then, \begin{equation} Q(\rho_\varepsilon\|\sigma_\varepsilon) \geq Q\left( \mathcal N(\rho_\varepsilon)\|\, \mathcal N(\sigma_\varepsilon) \right) \geq 0. \end{equation} \end{conjecture}

The functional at alpha zero is the real logarithm of
`Tr[A exp(log B - log A)]`. Matrix logarithms are continuous functional calculus;
regularized density matrices are positive definite. The conjecture includes both
monotonicity and nonnegativity. In the qubit counterexample, both output states are
also positive definite and the first inequality fails: the input trace is exactly
`50401283/7340144`, while the output trace is `1879639/266240`, which is strictly larger.

## Verified locator

DOI: `10.48550/arXiv.2606.31205`. Canonical source URL:
`https://arxiv.org/abs/2606.31205v1`. The source is Conjecture 15,
Section VIII.A, PDF p. 18. Regularization is Eq. `state_regularized`;
the functional is Eq. `regularized_Cu-Q`, evaluated at alpha zero.
