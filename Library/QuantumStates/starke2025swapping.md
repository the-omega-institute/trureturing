---
bibkey: starke2025swapping
authors: Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero
year: 2025
title: "Entanglement swapping for partially entangled qudits and the role of quantum complementarity"
doi: 10.48550/arXiv.2508.00813
url: https://arxiv.org/abs/2508.00813v2
claim: "The improved entanglement-swapping upper-bound conjecture, Eq. (59), bounds the average post-measurement l1 entanglement by the product of the input l1 entanglements divided by d-1."
strata_touched:
  - D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation
license: citation-only
triage: anchor
---

# Entanglement swapping for partially entangled qudits

D. S. Starke, M. L. W. Basso, L. C. Céleri and J. Maziero,
arXiv:2508.00813v2 (quant-ph). The source is the section
“The qutrit case and a conjecture”, p. 8, Eq. (59):

> Therefore, we conjecture that the improved upper bound has the form $\big\langle E_{l_1}\big(|\hat{\phi}_{pq}^{AB} \rangle\big) \big\rangle \le \frac{E_{l_1}(|\xi\rangle_{AC}) E_{l_1}(|\eta\rangle_{C'B})}{d-1}.$

The inputs (p. 4, Eqs. (19)–(20)) are
$|\xi\rangle_{AC}=\sum_j c_j|jj\rangle_{AC}$ and
$|\eta\rangle_{C'B}=\sum_k d_k|kk\rangle_{C'B}$, with
$\sum_j|c_j|^2=\sum_k|d_k|^2=1$.
The paper uses the unscaled entanglement measure (p. 4, Eq. (24)):

> $E_{l_1}(|\xi\rangle_{AC}) = \sum_{j\ne k}|c_j c_k|$.

The Bell measurement gives (p. 5, Eq. (30)):

> $\ket{\phi_{pq}^{AB}} = \frac{1}{\sqrt{d}}\sum_{k=0}^{d-1}c_{p\oplus k} d_k \bar{\omega}^{qk}|p\oplus k,k\rangle$.

Here $\omega=\exp(2\pi i/d)$, and $p\oplus k$ is addition modulo $d$.
The probability (p. 5, Eq. (31)) is:

> $\left\Vert\ket{\phi_{pq}^{AB}}\right\Vert^2 = \frac{1}{d}\sum_{k=0}^{d-1}|c_{p\oplus k}|^2 |d_k|^2 = \Pr\big(\Phi_{pq}^{CC'}\big)$.

The average (p. 5, Eq. (41)) is:

> $\big\langle E_{l_1}\big(|\hat{\phi}_{pq}^{AB} \rangle\big) \big\rangle = \sum_{p,q = 0}^{d-1} \Pr\big(\Phi_{pq}^{CC'}\big) E_{l_1}\big( |\hat{\phi}_{pq}^{AB} \rangle \big)$.

The Lean encoding renames the paper's second vector $d_k$ to $b_k$ and uses
`ZMod d` indices. Each post-measurement state is in Schmidt form
$\sum_k\alpha_k|\sigma(k),k\rangle$, with the bijection $\sigma(k)=p\oplus k$;
its entanglement is the ordered off-diagonal sum $\sum_{j\ne k}|\alpha_j\alpha_k|$.
Normalization divides the state by its Hilbert norm. Outcomes of probability
zero contribute zero.

For $d=4$ and $c=b=(7/10,1/10,7/10,1/10)$, both inputs are normalized and
have entanglement $39/25$. The average is $723/625$, exceeding the proposed
bound $(39/25)^2/3=507/625$.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2508.00813

Source: https://arxiv.org/abs/2508.00813v2

Conjecture: https://arxiv.org/html/2508.00813v2#S4.SS2,
Eq. (59), and https://arxiv.org/pdf/2508.00813v2, p. 8.
