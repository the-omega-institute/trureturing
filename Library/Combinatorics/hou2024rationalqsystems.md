---
bibkey: hou2024rationalqsystems
authors: J. Hou, Y. Jiang, Y. Miao
year: 2024
title: "Rational Q-systems at Root of Unity I. Closed Chains"
doi: 10.21468/SciPostPhys.16.5.129
url: https://arxiv.org/abs/2310.14966
claim: "Appendix C, conjecture (C.2), gives the primitive-state count with infinite Bethe roots."
strata_touched:
  - D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation
license: citation-only
triage: anchor
---

# Hou--Jiang--Miao rational Q-systems at a root of unity

J. Hou, Y. Jiang and Y. Miao, *Rational Q-systems at Root of Unity I. Closed Chains*,
arXiv:2310.14966v3 (2024), published as SciPost Phys. 16, 129 (2024),
doi: 10.21468/SciPostPhys.16.5.129.

## Source locator

Appendix C, page 35, states:

> Before introducing the algorithm, we make the following conjecture for the number of primitive states with infinite Bethe root(s) by observing the numerical results:
> \[
> N^{pri}_{±∞}(L, M, n_±) = \binom{L}{M − n_±} − \sum_{x=0}^{M−n_±−1} \binom{L}{x}, \tag{C.2}
> \]
> when n_± = n_+ = n_− is a solution to (3.15). When there is no solution to (3.15), N^{pri}_{±∞}(L, M, n_±) = 0.

The surrounding scope says: “We focus on the case with no twist, i.e. κ = 1 and η = iπ/3 for simplicity.” It considers even \(L\), primitive states with \(M \le L/2\), and equations (3.15)--(3.17) impose \(0 \le n_± \le 2\) and \(L \equiv 2(M-n) \pmod 6\) in this specialization.

## Verification boundary

This note records the citation and the verbatim source statement. The kernel-checked refutation is in `D5/S0/Certificates/Combinatorics/RationalQSystemInfinityCountRefutation.result`.

## Verified locator

- Source: https://arxiv.org/abs/2310.14966
- DOI: https://doi.org/10.21468/SciPostPhys.16.5.129
