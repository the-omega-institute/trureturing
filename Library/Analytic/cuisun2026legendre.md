---
bibkey: cuisun2026legendre
authors: Li-Li Cui and Zhi-Hong Sun
year: 2026
title: Curious identities involving Legendre polynomials and Apéry-like numbers
doi: 10.48550/arXiv.2607.12330
url: https://arxiv.org/abs/2607.12330v1
claim: Conjecture 2.1 asks for integral coefficient polynomials of every exact lower degree giving odd-power Legendre telescopers for all positive m and p.
strata_touched:
  - D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper
license: citation-only
triage: anchor
---

# Curious identities involving Legendre polynomials and Apéry-like numbers

The source is arXiv:2607.12330v1, by Li-Li Cui and Zhi-Hong Sun.

Equation (1.1), page 1:

> The famous Legendre polynomials {P_n(x)} are given by P_0(x) = 1, P_1(x) = x and (n + 1)P_{n+1}(x) = (2n + 1)xP_n(x) − nP_{n−1}(x) (n ≥ 1).

Conjecture 2.1, page 10:

> Suppose that m, p ∈ Z^+. Then there are integral polynomials f_i(t) with degree i (i = 0, 1, …, m − 1) such that (1 − x)^{m+1} Σ_{n=0}^{p−1} (2n + 1)^{2m+1} P_n(x) = pL_m(p, 1 − x)P_{p−1}(x) − pL_m(−p, 1 − x)P_p(x), where L_m(p, t) = (2p + 1)^{2m} t^m + f_{m−1}((2p + 1)^2) t^{m−1} + · · · + f_1((2p + 1)^2) t + f_0.

The coefficient family is read as independent of p, as in the explicit cases m = 1, 2, 3, 4 in Corollaries 2.1 and 2.5 and Theorems 2.4–2.5. The formal encoding takes each P_n in Q[X] and each f_i in Z[X]. The parameter of L ranges over Z to include the negative endpoint. Exact degree zero requires a nonzero constant coefficient. Equality in Q[X] includes x = 1 and requires no division by 1-x.

The paper supplies the definitions and conjecture, rather than a proof of the general statement. The associated formal result constructs all lower coefficient polynomials by iterating a degree-lowering integer operator and summing its finite inverse through the Legendre recurrence.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2607.12330

Source version: https://arxiv.org/abs/2607.12330v1
