---
bibkey: pudelko2025modular
authors: Marc T. Pudelko
year: 2025
title: Modular Periodicity of Random Initialized Recurrences
doi: null
url: https://arxiv.org/abs/2510.24882v5
claim: Conjecture 8 and equation (14) predict that the bounded-initialization probability of a Fibonacci absolute minimum at position zero converges to one quarter.
strata_touched:
  - D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation
license: citation-only
triage: anchor
---

# Modular periodicity of random initialized recurrences

Pudelko studies the Fibonacci recurrence and its parity analogue under random
integer initialization. Conjecture 8 states a proposed distribution for the
position of the absolute minimum, with value `P(0)=1/4` for position zero.
The following remark makes the probability operational for bounded integer
initializations in `[-N,N]^2`: equation (14) expects
`P_N(n)=P(n)+epsilon(N)` with `epsilon(N)` tending to zero as `N` tends to
infinity. The present formal statement uses this bounded-square reading for
the Fibonacci recurrence and position zero. A global minimum is allowed to be
tied, which gives position zero the largest count among the usual tie rules.

The repository refutes that clause by an unbounded family. For every natural
`t`, the number of initial pairs in the square of radius `6t` for which zero is
a global absolute-value minimizer is at most `30t^2+10t+1`. For `t>=3`, the
corresponding probability is at most `2/9`, so it cannot converge to `1/4`.
The bounded literature audit through 17 September 2026 found no later
independent proof or refutation of this clause. Exhaustive publication
priority remains unverified.

## Verified locator

- URL: https://arxiv.org/abs/2510.24882v5
- arXiv: 2510.24882v5, section 3, Conjecture 8, equation (13), and the
  bounded-initialization remark containing equation (14).
