---
bibkey: hoffmanrizzoloslivken2015pattern
authors: Christopher Hoffman, Douglas Rizzolo, and Erik Slivken
year: 2015
title: "Pattern-avoiding permutations and Brownian excursion, Part II: Fixed points"
doi: 10.48550/arXiv.1506.04174
url: https://arxiv.org/abs/1506.04174v1
claim: "Theorem 1.1 gives fixed-point scaling limits for uniform 231- and 123-avoiding permutations, implying the 231 derangement proportion tends to 0 and the 123 proportion tends to 9/16."
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed points in 123- and 231-avoiding permutations

Hoffman, Rizzolo, and Slivken's Theorem 1.1(a) states that the fixed-point
counting measure of a uniform 231-avoiding permutation, after multiplication
by `n^(-1/4)`, converges weakly to
`(2^(7/4) * sqrt(pi))^(-1) * e(t)^(-3/2) dt`. Its total mass is positive
almost surely. If `N_n` is the number of fixed points, then
`n^(-1/4) * N_n` converges in distribution to a random variable `X` with
`P(X = 0) = 0`. The closed-set Portmanteau bound therefore gives
`limsup P(N_n = 0) <= P(X = 0) = 0`, so the 231-avoidance derangement
proportion tends to zero.

Theorem 1.1(b) states that the centered fixed-point counting measure of a
uniform 123-avoiding permutation converges weakly to
`A * delta_{-e(1/2)/2} + B * delta_{e(1/2)/2}`, where `A` and `B` are
independent Bernoulli random variables with parameter `1/4`. Taking total
mass gives `N_n` converging in distribution to `A + B`. Since these variables
are integer-valued, the continuity interval `(-1/2, 1/2)` yields
`P(N_n = 0) -> P(A + B = 0) = (3/4)^2 = 9/16`.

This is prior literature that settles Vatter's 2026 Conjecture 4.1 and
Question 4.2. It is not a new repository theorem and has no formal D5
declaration attached to it.

## Verified locator

- arXiv: https://arxiv.org/abs/1506.04174v1
- HTML: https://arxiv.org/html/1506.04174v1, Theorem 1.1(a)-(b)
- DOI: https://doi.org/10.48550/arXiv.1506.04174
- Submitted June 12, 2015 (version v1)
