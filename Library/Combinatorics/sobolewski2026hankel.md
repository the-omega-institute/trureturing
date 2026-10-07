---
bibkey: sobolewski2026hankel
authors: Bartosz Sobolewski, Maciej Ulas
year: 2026
title: "Hankel determinants of weighted binary sums of digits"
doi: 10.48550/arXiv.2607.09376
url: https://arxiv.org/abs/2607.09376v1
claim: "Recursions and closed forms for Hankel determinants of weighted binary digit sums; vanishing of the determinants at t = 2ζ on a structured index set and a conjectured exact description of the nonvanishing indices (Conjecture 5.7)."
strata_touched:
  - D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel
  - D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankel
license: citation-only
triage: anchor
---

# Sobolewski and Ulas, Hankel determinants of weighted binary sums of digits

For u = Σ_j ε_j 2^j with binary digits ε_j and weights w_j, the weighted digit sum is s_w(u) = Σ_j ε_j w_j, and
H_w(n) = det[s_w(i+j)]_{0≤i,j<n}. The paper derives a general recursion for H_w(n), closed forms along several index
sequences for the ordinary digit sum, and, for w_j = t^j, studies the polynomial determinants H(n,t).

For t = 2ζ with ζ a primitive d-th root of unity, Theorem 5.4 shows that H(n,2ζ) vanishes on a structured set A_d,
and Conjecture 5.7 states that it vanishes exactly there. For d = 2 the conjecture reads: H(n,−2) ≠ 0 if and only if
n is one of n_k − 1, n_k, n_k + 1, where n_k = ⌈2^{k+2}/3⌉.

The module `D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel` proves the case d = 2.

## Verified locator

DOI: 10.48550/arXiv.2607.09376

URL: https://arxiv.org/abs/2607.09376v1

- Locator: Section 4, Theorem 4.4.
- Locator: Section 5.1, Theorem 5.4, Conjecture 5.7 and the sentence following it.
