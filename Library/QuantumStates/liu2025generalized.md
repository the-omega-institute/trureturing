---
bibkey: liu2025generalized
authors: Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura
year: 2025
title: "Generalized Concentratable Entanglement via Parallelized Permutation Tests"
doi: 10.1103/jtlj-qs3y
url: https://arxiv.org/abs/2406.18517v1
claim: "For an n-qubit pure state the generalized concentratable entanglement is C^{(K)}(s) = (1 - 2^{-|s|} sum over all subsets alpha of s of Tr(rho_alpha^K)) / (K - 1), with Tr(rho_emptyset^K) = 1, for any real K > 1. The paper conjectures, from Haar-random numerics, that C^{(K)}(s') <= C^{(K)}(s) whenever s' is a subset of s and that C^{(K)} is subadditive on disjoint sets, both for every real K > 1; both statements are proved for K = 2 by Beckey et al."
strata_touched:
  - D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation
license: citation-only
triage: anchor
---

# Generalized Concentratable Entanglement via Parallelized Permutation Tests

Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang and Jordi Tura, Phys. Rev.
Research 7, L032022 (2025); arXiv:2406.18517v1. Quotations are from the arXiv
source.

The definition (Eq. (defeq)):

> $\mathcal{C}^{(K)}_{\ket{\psi}}(s):=\frac{1}{K-1}\left(1-\frac{1}{2^{|s|}}\sum_{\alpha\in\mathcal{P}(s)}\Tr(\rho_{\alpha}^K)\right)$ for any $K>1$. […] $\rho_{\alpha}$ denotes the corresponding reduced density matrix of subsystem $\alpha\in\mathcal{P}(s)$ where $\rho=\ketbra{\psi}$. We take $\Tr(\rho^K_{\varnothing})=1$ in the sum.

The conjecture (arXiv Conjecture 6; journal Conjecture 1):

> The GCE has the following properties: 1. $\mathcal{C}^{(K)}_{\ket{\psi}}(s')\leqslant \mathcal{C}^{(K)}_{\ket{\psi}}(s)$ if $s'\subseteq s$. 2. Subadditivity: $\mathcal{C}^{(K)}_{\ket{\psi}}(s\cup s')\leqslant \mathcal{C}^{(K)}_{\ket{\psi}}(s) + \mathcal{C}^{(K)}_{\ket{\psi}}(s')$ for $s\cap s'=\varnothing$.

with the reading

> These two conjectures have been proven to be true for $K=2$ […]. Based on these arguments we here conjecture that they also hold for $K>1$.

The encoding takes `Tr(ρ_α^K)` as the real part of the trace of the
continuous-functional-calculus power of the existing `reducedState`, with the
empty set contributing 1, and states clause 1 for every number of qubits,
every normalized state, all `s' ⊆ s` and every real `K > 1`.

## Verified locator

- DOI: https://doi.org/10.1103/jtlj-qs3y (Phys. Rev. Research 7, L032022
  (2025); DOI and article number from Crossref).
- URL: https://arxiv.org/abs/2406.18517v1 (v1, 2024-06-26, the only version;
  source `apssamp.tex`, md5 `6833fead90a78090189f33e44f72b503`): the
  definition (l. 161–172), the conjecture (l. 386–392), its reading for
  `K > 1` (l. 403–405) and the numerical evidence (Fig. 3, l. 397).
