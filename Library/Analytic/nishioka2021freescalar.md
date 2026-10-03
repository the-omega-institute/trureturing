---
bibkey: nishioka2021freescalar
authors: Tatsuma Nishioka; Yoshiki Sato
year: 2021
title: "Free energy and defect C-theorem in free scalar theory"
doi: 10.1007/JHEP05(2021)074
url: https://arxiv.org/abs/2101.02399v5
claim: "For every k >= 0, -2^(-2k-2)/(k+1) H_(2k+1) - sum_(m=1)^k 2^(-2k-2)(2^(2m)-2)/(k-m+1) B_(2m)/(2m) + sum_(j=0)^(2k+1) (-1)^j/2^(2k-j) C(2k+1,j) H_j zeta(-j) + (1-2^(-2k-1)) H_(2k+1) B_(2k+2)/(k+1) = 0 (eq. (C.12), conjectured: checked up to k = 100, no proof known to the authors)."
strata_touched:
  - D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity
license: citation-only
triage: anchor
---

# Free energy and defect C-theorem in free scalar theory

T. Nishioka and Y. Sato, arXiv:2101.02399 (v1 2021-01-07, v5 2021-06-02);
JHEP 05 (2021) 074. Subject: hep-th.

The paper computes the free energy of a conformally coupled free scalar on
hyperbolic space `H^d` through its spectral zeta function. For even `d` the
derivative `∂_s ζ_{H^d}(0, 1/2)` contains, besides the values `ζ'(−j)`, a
bracket of harmonic numbers `H_j`, Bernoulli numbers `B_n` and zeta values
`ζ(−j)`. The authors write:

> Now we would like to show a sum of the terms except ζ'(−j) in the bracket
> vanishes,
> −2^{−2k−2}/(k+1) H_{2k+1} − Σ_{m=1}^{k} 2^{−2k−2}(2^{2m}−2)/(k−m+1) · B_{2m}/(2m)
> + Σ_{j=0}^{2k+1} (−1)^j/2^{2k−j} · C(2k+1, j) · H_j ζ(−j)
> + (1 − 2^{−2k−1}) H_{2k+1} B_{2k+2}/(k+1) = 0.
> For k = 0, the summation term Σ_{m=1}^{k} should be omitted. We confirmed
> (C.12) up to k = 100 numerically. However, we do not know a proof of (C.12).

## Verified locator

- DOI: https://doi.org/10.1007/JHEP05(2021)074 (open-access PDF retrieved
  2026-09-30): appendix C, eq. (C.12); used in eq. (4.21).
- URL: https://arxiv.org/abs/2101.02399v5 (source of v5 retrieved 2026-09-30):
  appendix A, eq. `conjecture1`; used in eq. `hyp_even_der_zeta`.
