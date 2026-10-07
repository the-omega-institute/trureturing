---
bibkey: huynhvu2024universal
authors: Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani
year: 2024
title: "Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum"
doi: 10.1103/PhysRevA.109.042402
url: https://arxiv.org/abs/2311.00806v2
claim: "Conjecture 3: Consider a spin ensemble. Perform the precession protocol with odd K ≥ 3 on the total angular momentum of the system. If the score P_K > 𝐏_K^conj is obtained, then the spin ensemble is GME."
strata_touched:
  - D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/PhysRevA.109.042402

Source: https://arxiv.org/abs/2311.00806v2

Conjecture 3, Result 4 and its piecewise threshold: PDF p. 9. Result 4 asserts certification for odd 3 ≤ K ≤ 21, total constituent spin at most 15, and score greater than the threshold plus 10^{−11}.
The precession protocol, Eqs. (1)–(3): PDF p. 2.
The definitions of separability and GME: PDF p. 3.

# Universal precession threshold

Conjecture 3 states:

> Consider a spin ensemble. Perform the precession protocol with odd $K \geq 3$ on the total angular momentum of the system. If the score $P_K > \mathbf{P}_K^{\text{\normalfont{conj}}}$ is obtained, then the spin ensemble is GME.

The score is $P_K = \operatorname{tr}(\rho Q_K)$, with
$Q_K = K^{-1}\sum_{k=0}^{K-1}\operatorname{pos}(J_k)$ and
$J_k = \cos(2\pi k/K)J_x + \sin(2\pi k/K)J_y$.
The function `pos` assigns weight one to positive eigenvalues, one half to
zero eigenvalues, and zero to negative eigenvalues.

The source defines the state notions by:

> With these notations, a state $\rho_{\mathbf{J},\mathbf{J}^\complement}$ of a spin ensemble is separable over the $\mathbf{J}$-$\mathbf{J}^\complement$ bipartition if $\rho_{\mathbf{J},\mathbf{J}^\complement} = \sum_k p_k \rho_{\mathbf{J},k} \otimes \rho_{\mathbf{J}^\complement,k}$, where $\rho_{\mathbf{J},k}$ (or $\rho_{\mathbf{J}^\complement,k}$) is a state within the subspace $\bigotimes_{j\in\mathbf{J}}\mathcal{H}^{(j)}$ (or $\bigotimes_{j'\in\mathbf{J}^\complement}\mathcal{H}^{(j')}$). Conversely, $\rho_{\text{GME}}$ is GME if it is not a convex combination of states separable over any bipartition $\mathbf{J}$: that is, $\rho_{\text{GME}} \neq \sum_{\mathbf{J}} p_{\mathbf{J}} \rho_{\mathbf{J},\mathbf{J}^\complement}$.

The separate note `huynhvu2024precession` concerns Conjecture 2, the
$\{1,K/2\}$ separable bound, from the same paper.
