---
bibkey: cope2021binarydetection
authors: T. Cope
year: 2021
title: The Binary-Outcome Detection Loophole
doi: 10.1088/1367-2630/ac10a5
url: https://arxiv.org/abs/2005.03344v3
claim: The binary-outcome detection threshold has the bound 2(m_A+m_B-8)/(m_A m_B-16), and Section 4.3 conjectures eta* = 4/(m+4) for the symmetric m-input case.
strata_touched:
  - D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation
license: citation-only
triage: anchor
---

The paper studies the binary-outcome detection loophole, gives the bound `2(m_A+m_B-8)/(m_A m_B-16)`, and conjectures in Section 4.3 that the symmetric binary-outcome detection threshold is `eta* = 4/(m+4)` for `m` inputs per party.

## Verified locator

DOI: https://doi.org/10.1088/1367-2630/ac10a5

Source: https://arxiv.org/abs/2005.03344v3

## Source statements

Section 4.3, arXiv v3 p. 6:

> In order to prove that our conjecture of $\eta^*=4/(m+4)$ for $m_{\mathrm{A}}=m_{\mathrm{B}}=m$ is correct, one would need to provide a extremal $\mathcal{NS}$ distribution $p^{\mathrm{NS}}$, and corresponding Bell inequality $s_{a'b'}^{xy}$, such that $\sum_{a',b',x,y}s_{a'b'}^{xy}p^{\mathrm{NS}}_{\eta}(a'b'|xy) \not \leq k,\; \forall \eta > \eta^*$.

The symmetric conjecture concerns every input count m. The formal refutation uses m = 13; the detected outputs are Bool and failure is none in Option Bool.

Section 2, arXiv v3 pp. 2–3:

> However, we do assume that Alice and Bob can isolate their systems, also referred to here as devices, from communicating with each other.

> The model considered here adds an extra output to both parties to alter the original distribution $p(ab|xy)$ in the following way:

> These distributions may always be expressed as convex combinations of deterministic distributions $p(ab|xy)=\delta_{a,a_x}\delta_{b,b_y}$, which are finite in number.

> We will refer to $\eta^*$ as the no-signalling threshold.
