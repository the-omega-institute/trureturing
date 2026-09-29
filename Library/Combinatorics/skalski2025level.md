---
bibkey: skalski2025level
authors: Tomasz Skalski, Tomasz Stroiński
year: 2025
title: Level sets and maximum likelihood estimation for the Ising model
doi: 10.48550/arXiv.2511.20925
url: https://arxiv.org/abs/2511.20925v1
claim: The paper bounds the smallest set of uniqueness u(k,q) for the nonnegative cone of the Walsh space B^k_q on the cube {-1,+1}^k and conjectures u(k,2) = k + 1.
strata_touched:
  - D5/S3/Combinatorics/IsingUniquenessSets
license: citation-only
triage: anchor
---

# Level sets and maximum likelihood estimation for the Ising model

Skalski and Stroiński study the existence of maximum likelihood estimators in
the discrete exponential family of the Ising model through sets of uniqueness,
following Bogdan, Bosy and Skalski. On `X = {-1,+1}^k` they set
`r_j(x) = x_j`, `w_L(x) = ∏_{j∈L} r_j(x)` and, for `1 ≤ q ≤ k`,

> B^k_q = Lin{w_L : L ⊂ {1,…,k} and |L| ≤ q}.

A subset `U ⊂ X` is a set of uniqueness for `(B^k_q)_+`, the nonnegative
functions of `B^k_q`, when `φ = 0` is the only such function vanishing on `U`,
and `u(k,q)` is the size of the smallest one. Lemma rem:three states that the
points with exactly one coordinate `+1`, together with `(+1,…,+1)`, form a
set of uniqueness for `(B^k_2)_+`; the closing theorem of the section on
extremal sizes lists `log k + ½ log log k + O(1) ≤ u(k,2) ≤ k+1` and
`u(k,k) = 2^k`, and the section ends with the conjecture

> u(k,2)=k+1, i.e., for every k there are no sets of uniqueness having at
> most k elements.

At `k = 2` the space `B^2_2` is all of `ℝ^X`, so `u(2,2) = 4`, as the listed
`u(k,k) = 2^k` also gives; the upper bound `k + 1` and Lemma rem:three hold
from `k = 3` on.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2511.20925
- URL: https://arxiv.org/abs/2511.20925v1
- Version and location: arXiv:2511.20925v1 (2025-11-25), section on sets of uniqueness and Rademacher functions, Lemma rem:three, and the closing theorem and conjecture of the section on extremal sizes of sets of uniqueness.
