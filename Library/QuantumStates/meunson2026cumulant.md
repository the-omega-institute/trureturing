---
bibkey: meunson2026cumulant
authors: A. Meunson; T. Deesuwan
year: 2026
title: "Cumulant-based quantum relative Rényi functional"
doi: 10.48550/arXiv.2606.31205
url: https://arxiv.org/abs/2606.31205v1
claim: "Conjecture 15 asserts that Q = -S_0^Q decreases under commutativity-preserving channels for noncommuting regularized states with output support inclusion; the abstract and conclusion state that the quantum data-processing inequality of the cumulant-based functional for alpha > 1 under arbitrary CPTP maps remains open."
strata_touched:
  - D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation
  - D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation
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

## Data processing for alpha > 1

The abstract states the open question; the source sentences are quoted verbatim.

> On its natural non-regularized domain for $\alpha>1$ under the support condition $\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma)$, we establish several fundamental properties, including positivity, reduction to the classical case, additivity, unitary invariance, continuity, and monotonicity with respect to the Rényi parameter $\alpha$. Whether the functional satisfies the quantum data-processing inequality (QDPI) under arbitrary CPTP maps remains open.

The conclusion repeats it:

> The validity of the quantum data-processing inequality remains open.

Definition 3 (Section IV, Eq. `QCRRF`), verbatim with line breaks joined:

> Let $\rho$ and $\sigma$ be density operators in $\mathcal{D}(\mathcal{H})$. For $\alpha >1$, the cumulant-based quantum relative Rényi functional (Cu-Q relative Rényi functional) is defined as \begin{equation} \label{QCRRF} \begin{split} &S_\alpha^{\text{Q}}(\rho \| \sigma) \\ &:= \begin{cases} \dfrac{1}{\alpha - 1} \ln \operatorname{Tr} \left( \rho e^{(\alpha - 1) (\ln \rho - \ln \sigma)} \right), & \text{if } (\rho, \sigma) \in \mathcal{R}, \\ +\infty, & \text{otherwise.} \end{cases} \end{split} \end{equation}

Section III defines the admissible set; in paraphrase, $\mathcal{R} := \{ (\rho,\sigma) \in \mathcal{D}(\mathcal{H}) \times \mathcal{D}(\mathcal{H}) \mid \rho \not\perp \sigma \text{ and } \operatorname{supp}(\rho) \subseteq \operatorname{supp}(\sigma) \}$.
The data-processing inequality (Section III), verbatim:

> Specifically, for $(\rho,\sigma )\in \mathcal{D}(\mathcal{H}) \times \mathcal{D}(\mathcal{H})$ with $\mathrm{supp}(\rho)\subseteq\mathrm{supp}(\sigma)$, any CPTP map $\mathcal{N}_{CPTP}$ satisfies: \begin{equation} S_{\alpha}(\rho \| \sigma) \ge S_{\alpha}\bigl(\mathcal{N}_{CPTP}(\rho)\| \mathcal{N}_{CPTP}(\sigma)\bigr), \end{equation} under the following parameter regimes:

Section VIII.C (PDF p. 21) reports that a preliminary study (J. Phys.: Conf. Ser. 3168 (2025) 012014)
observed no violations of QDPI within $\alpha\in(0.9,1.3)$ over $10^4$ random qubit pairs
per run, ten runs, and four channels.

## Verified locator

DOI: `10.48550/arXiv.2606.31205`. Canonical source URL:
`https://arxiv.org/abs/2606.31205v1`. The source is Conjecture 15,
Section VIII.A, PDF p. 18. Regularization is Eq. `state_regularized`;
the functional is Eq. `regularized_Cu-Q`, evaluated at alpha zero.
The alpha > 1 question is stated in the abstract and in the Conclusion;
Definition 3 is Eq. `QCRRF` in Section IV.
