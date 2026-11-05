---
bibkey: mirzavaziri2026gaussianquotient
authors: Madjid Mirzavaziri, Daniel Yaqubi
year: 2026
title: Graph binomial coefficients and a positivity conjecture of Guo and Krattenthaler
doi: 10.48550/arXiv.2610.19249
url: https://arxiv.org/abs/2610.19249v1
claim: "Problem 7.2 asks whether weak increase of the first Gaussian quotient through its middle forces the two-exception sign pattern after a second q-integer division."
strata_touched:
  - D5/S3/Combinatorics/GaussianQuotient/MirzavaziriYaqubiMonotonicityRefutation
license: citation-only
triage: anchor
---

# Gaussian quotient monotonicity and coefficient signs

## Verified locator

DOI: 10.48550/arXiv.2610.19249

URL: https://arxiv.org/abs/2610.19249v1

Problem 7.2 appears on page 16. The source TeX is `gk74-2.tex` from
https://arxiv.org/e-print/2610.19249v1, sha256
`8e15a5d14b845dcc082a0a0e819126ca875269aa6f166737d163c7a88a8dd865`.

## Source statement

The Gaussian bracket below expands the source macro `\qbin` without changing its typography.

> Characterize the quadruples $(N,k,a,b)$ for which $\genfrac{[}{]}{0pt}{}{N}{k}_q/([a]_q[b]_q)$ is a polynomial whose only negative coefficients are $-1$ at $q^1$ and at $q^{D-1}$. In particular, is this always the case when $\genfrac{[}{]}{0pt}{}{N}{k}_q/[a]_q$ is weakly increasing from $q^1$ to its middle coefficient?

The next sentence on page 16 states:

> By Lemma 4.1, the answer to the last question is affirmative as soon as, in addition, the coefficients of $q^{b}$ and $q^{b+1}$ in $\genfrac{[}{]}{0pt}{}{N}{k}_q/[a]_q$ are distinct.

The final question is encoded using integer polynomials U and P, positive a,b,
k ≤ N, and exact multiplication equalities for the quotients. Weak increase
starts at the comparison of coefficients one and two and ends at
floor(natDegree U / 2). The exceptional indices are 1 and natDegree P − 1.
Natural-index subtraction is truncated at zero. The Gaussian and q-integer
definitions are reused from their existing polynomial owners.

## Scope of the negative answer

The finite counterexample has (N,k,a,b)=(30,3,7,10), degrees 75 and 66 for U
and P, and coefficient −1 at degree 11 in P. It answers the final sufficiency
question. The full classification and an unbounded counterexample family are
separate questions. Lemma 4.1 retains its additional strictness hypothesis;
the counterexample has equal coefficients u10=u11=3.

Exact computations are available in `the-omega-institute/trureturing-experiments`,
commit `c9ab263c1e90358645b266282e0d0c168e7f2523`, under
`docs/reports/mirzavaziri-yaqubi-2026-gaussian-quotient-monotonicity-problem-7-2/`.
The command `python3 docs/reports/mirzavaziri-yaqubi-2026-gaussian-quotient-monotonicity-problem-7-2/check.py`
exited 0 with `ALL_CHECKS_OK`; `check.py` has sha256
`f67ed55ee555037daf83cc71c4e7a3dc4faea2839d4e00abc80689cfb5528a99`.
The finite computations do not prove the universal family assertion.

## Literature boundary

Issue [#21322](https://github.com/the-omega-institute/trureturing/issues/21322)
records the bounded source and literature screen. No exact settlement was
identified there. Completeness of the screen is ASSUMED-UNVERIFIED; Semantic
Scholar returned HTTP 429, and several web responses were ineffective.
