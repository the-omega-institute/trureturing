---
bibkey: zelinskyzhang2025klprimitive
authors: Joshua Zelinsky; Kyle Zhang
year: 2025
title: "Kullback-Leibler divergence and primitive non-deficient numbers"
doi: 10.48550/arXiv.2501.04209
url: https://arxiv.org/abs/2501.04209v2
claim: "Conjecture 22: for every positive integer n outside {1, 12, 24, 30, 36, 48, 60, 72, 120, 180, 240, 360}, if p is the smallest prime factor of n, then v(n) >= 1/p^2, where v(n) is the divisor-weighted logarithmic sum defined in the paper."
strata_touched:
  - D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation
license: citation-only
triage: anchor
---

# Kullback-Leibler divergence and primitive non-deficient numbers

Zelinsky and Zhang define, for a positive integer n,

`v(n) = sum_{d | n, d > 1} (1/d) log((tau(n) - 1)/d)`.

On page 14, Conjecture 22 states that every positive integer outside the twelve
listed exclusions satisfies `v(n) >= 1/p^2`, where p is its smallest prime
factor.

## Verified locator

- DOI: 10.48550/arXiv.2501.04209
- URL: https://arxiv.org/abs/2501.04209v2
- Locator: arXiv:2501.04209v2, page 14, Conjecture 22.

The current arXiv record lists versions v1 and v2. The result formalized in the
named stratum refutes the literal universal statement at n = 6.
