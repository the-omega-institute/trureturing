---
bibkey: zelinskyzhang2025klprimitive
authors: Joshua Zelinsky; Kyle Zhang
year: 2025
title: "Kullback-Leibler divergence and primitive non-deficient numbers"
doi: 10.48550/arXiv.2501.04209
url: https://arxiv.org/abs/2501.04209v2
claim: "Conjecture 22 asserts that every positive integer n outside {1, 12, 24, 30, 36, 48, 60, 72, 120, 180, 240, 360} satisfies v(n) >= 1/p^2 for its smallest prime factor p and the paper's divisor-weighted logarithmic sum v, while Conjecture 15 asserts that infinitely many positive integers are deficient and KL-primitive."
strata_touched:
  - D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation
  - D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive
license: citation-only
triage: anchor
---

# Kullback-Leibler divergence and primitive non-deficient numbers

Zelinsky and Zhang define, for a positive integer n,

`v(n) = sum_{d | n, d > 1} (1/d) log((tau(n) - 1)/d)`.

On page 14, Conjecture 22 states that every positive integer outside the twelve
listed exclusions satisfies `v(n) >= 1/p^2`, where p is its smallest prime
factor.

Equation (6) defines `KL(n) = sum_{d | n} d log(d/(2 phi(d)))`.
On page 12, Definition 1 says that n is KL-primitive if "KL(n) >= 0,
and KL(d) < 0 for any d|n with d < n". On the same page,
Conjecture 15 states: "There are infinitely many n which are deficient
and KL-primitive." Here deficient means `sigma(n) < 2n`.

## Verified locator

- DOI: 10.48550/arXiv.2501.04209
- URL: https://arxiv.org/abs/2501.04209v2
- Locator: arXiv:2501.04209v2, page 14, Conjecture 22.
- Locator: arXiv:2501.04209v2, page 12, Definition 1 and Conjecture 15; KL is defined in Equation (6).

The current arXiv record lists versions v1 and v2.
