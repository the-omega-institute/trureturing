---
bibkey: jametpopolistoll2021maximum
authors: Damien Jamet and Pierre Popoli and Thomas Stoll
year: 2021
title: Maximum order complexity of the sum of digits function in Zeckendorf base and polynomial subsequences
doi: 10.48550/arXiv.2106.09959
claim: The parity sequence of the Zeckendorf digit sum along a polynomial subsequence of degree d has maximum order complexity conjecturally of order N raised to one over two d.
strata_touched:
  - D5/S0/Conventions/WDigits
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S1/Words/Complexity/MorseHedlund
license: citation-only
triage: anchor
---

# Maximum order complexity of the sum of digits function in Zeckendorf base and polynomial subsequences

Jamet, Popoli, and Stoll study the binary sequence `s_Z(P(n)) mod 2`, where `s_Z`
is the Zeckendorf digit sum and `P` is a polynomial, under the maximum order
complexity measure `M(S,N)`. They prove the lower bound of order `N^(1/(2d))`
for monic integer `P` of degree `d >= 2` mapping the naturals into themselves,
and state the matching upper bound as Conjecture 3. The paper records that the
Zeckendorf case is algorithmically harder than the binary case and that their
computations do not exceed `10^9` terms.

This note is the literature anchor for the problem candidate
`Problems/zeckendorf-polynomial-maximum-order-complexity.md`.

## Search log

- 2026-08-18: Queried the arXiv Atom API for `id_list=2106.09959`. HTTP 200 with
  `totalResults=1`; the entry resolved to `http://arxiv.org/abs/2106.09959v1`,
  title *Maximum order complexity of the sum of digits function in Zeckendorf
  base and polynomial subsequences*, authors Damien Jamet, Pierre Popoli, and
  Thomas Stoll, published 2021-06-18, primary category `math.NT`. The API
  reported no `arxiv:doi` and no `arxiv:journal_ref`, so the arXiv-assigned DOI
  is used.
- 2026-08-18: Issued `HEAD https://doi.org/10.48550/arXiv.2106.09959`, which
  returned HTTP 302 redirecting to `https://arxiv.org/abs/2106.09959`.

No literature search for a later resolution of Conjecture 3 was performed; the
open status recorded in the problem candidate is the status stated in this
arXiv version.

## Verified locator

- arXiv: https://arxiv.org/abs/2106.09959
- DOI: https://doi.org/10.48550/arXiv.2106.09959
