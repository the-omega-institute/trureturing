---
bibkey: inestaetal2026entanglementbuffering
authors: Álvaro G. Iñesta; Bethany Davies; Sounak Kar; Stephanie Wehner
year: 2026
title: "Entanglement buffering with multiple quantum memories"
doi: 10.1038/s41534-025-01161-3
url: https://arxiv.org/abs/2502.20240v1
claim: "The paper models an entanglement buffer with one long-lived memory and n short-lived generation memories, with probabilistic generation, consumption, depolarising decay and probabilistic purification governed by coefficients a_k, b_k, c_k, d_k; it derives closed-form formulas for the availability and the average consumed fidelity, proves that the availability is non-increasing in the purification probability q, gives policy-independent bounds, and conjectures that the availability at q = 1 of the always-failing policy (c_k = d_k = 0) is a tight lower bound for every purification policy."
strata_touched:
  - D5/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound
license: citation-only
triage: anchor
---

# Entanglement buffering with multiple quantum memories

Á. G. Iñesta, B. Davies, S. Kar and S. Wehner, arXiv:2502.20240v1 (only version); npj Quantum Information 12 (2026), 64. Quotations are from the v1 TeX source; displayed macros are expanded without changing the wording.

The decay of the buffered link:

> The entangled link stored in G is subject to *depolarising noise* with memory lifetime $1/\Gamma$, which causes an exponential decay in fidelity with rate $\Gamma$. That is, if the link in memory has an initial fidelity $F$, after time $t$ this reduces to $F \mapsto \left(F-\frac{1}{4}\right) e^{-\Gamma t} + \frac{1}{4}.$

Purification policies:

> The *purification policy* $\pi$ is a function that indicates the purification protocol that must be used when $k$ links are generated in the B memories, $\pi: k \in \{1, \dots,n\} \mapsto \pi(k) \in \mathcal{P}_{k+1}$, where $\mathcal{P}_{m}$ is the set of all $m$-to-1 purification protocols.

> The purification protocol updates the fidelity of the buffered link from $F$ to $J_k(F)$, where $J_k(F) = \frac{1}{4} + \frac{a_k(\rho_{\mathrm{new}})\left(F-\frac{1}{4}\right)+b_k(\rho_{\mathrm{new}})}{c_k(\rho_{\mathrm{new}})\left(F-\frac{1}{4}\right)+d_k(\rho_{\mathrm{new}})}.$

> The protocol succeeds with probability $p_k(F) = c_k(\rho_{\mathrm{new}}) \left(F-\frac{1}{4}\right) + d_k(\rho_{\mathrm{new}})$, otherwise all of the links (including the buffered one) are discarded and the G memory becomes empty.

Availability (Definition `def.A`):

> The availability $A$ is the probability that there is an entangled link present in memory G when a consumption request arrives.

Theorem 1 (`theorem.A`) states $A = \mathbb{E}[T_\mathrm{occ}]/(\mathbb{E}[T_{\mathrm{gen}}]+\mathbb{E}[T_\mathrm{occ}])$ a.s., with $\mathbb{E}[T_{\mathrm{gen}}] = 1/(1- (1-p_{\mathrm{gen}})^n)$ and
$$\mathbb{E}[T_\mathrm{occ}] = \frac{1-\tilde{A}+\tilde{C} (F_\mathrm{new}-\frac{1}{4})}{\big[(1-\tilde{A})(1-\tilde{D}) - \tilde{B}\tilde{C} \big] \tilde{P} },$$
where $\tilde P=p_{\mathrm{con}}+ q(1- (1-p_{\mathrm{gen}})^n)(1-p_{\mathrm{con}})$. The coefficients $\tilde A,\tilde C$ and $\tilde B,\tilde D$ are $q(1-p_{\rm con})$ times the binomially weighted sums $\tilde a,\tilde c$ and $\tilde b,\tilde d$ of the policy coefficients, divided by $e^{\Gamma}-(1-q+q(1-p_{\mathrm{gen}})^n)(1-p_{\mathrm{con}})$ and by $\tilde P$ respectively.

Appendix C, on the admissible coefficients:

> Since $p_k$ is a probability, we must enforce $0 \leq p_k \leq 1$.

> This output fidelity must also be between $1/4$ (fully depolarized state) and $1$ (perfect Bell pair).

The conjecture (after Corollary 1):

> Unlike the upper bound, we note that the lower bound from (\ref{eq.A_bounds}) has not yet shown to be tight. We believe that the availability at $q=1$ of a policy that always fails purification ($c_k=d_k=0$, $\forall k$) constitutes a tight lower bound for any other purification policy. We leave this proof as future work.

## Verified locator

Source: https://arxiv.org/abs/2502.20240v1
- URL: https://arxiv.org/abs/2502.20240v1 (the e-print is a tar archive; member `main.tex`, md5 `c1b5c2a56b45349a94ac22e6fde7bd87`, 2402 lines):
  - the depolarising decay, l. 223–228;
  - the purification policy, the jump function and the success probability, l. 247–265;
  - availability, l. 344–354;
  - Theorem 1, l. 378–415;
  - Corollary 1 and the conjecture, l. 479–502;
  - the admissible coefficients, Appendix C, l. 1734–1767.
- DOI: 10.1038/s41534-025-01161-3 (https://doi.org/10.1038/s41534-025-01161-3; Crossref lists npj Quantum Information, volume 12, issue 1, article 64, published 20 February 2026). The journal text keeps the conjecture and its "future work" sentence verbatim.
