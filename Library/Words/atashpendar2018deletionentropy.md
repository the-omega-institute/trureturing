---
bibkey: atashpendar2018deletionentropy
authors: Arash Atashpendar, David Mestel, A. W. Roscoe, and Peter Y. A. Ryan
year: 2018
title: A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics
doi: null
url: https://arxiv.org/abs/1807.11609
claim: "Section V asks whether positional autocorrelation determines the entropy ordering of finite binary deletion-channel outputs; Section IV-E.3 and Table I specify the proposed order."
strata_touched:
  - D5/S3/Entropy/DeletionChannelEntropyOrdering
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/1807.11609

The statements below are from arXiv:1807.11609v1, printed pages 3, 4, 7 and 10.

## Finite entropy ordering

Section V, page 10, states:

> Beyond establishing this maximization, proving the entropy ordering of x strings determined by κ2(x) for finite n and m represents another open problem.

Section IV-E.3, page 10, states:

> our numerical results indicate that κ2(x) predicts the entropy ordering perfectly in the finite length domain as well, i.e., for small and comparable fixed values of n and m. An example obtained from empirical data is presented in Table I to illustrate the correlation between Hn(x) and κ2(x) for n = 8 and m = 5.

Table I is headed “x STRINGS SORTED BY κ2 IN DESCENDING ORDER PREDICTS THE ENTROPY ORDERING”. It orders larger autocorrelation before smaller entropy.

## Definitions and indices

Section III-A.f, page 3, states:

> Let ωx(y) denote the number of distinct ways that y can project to x:

Its displayed formula is ωx(y) := |{π ∈ P([n]) : yπ = x}|. The next sentence states:

> we refer to the number of masks associated with a pair (y, x) as the weight of y, i.e., the number of times x can be embedded in y as a subsequence.

Equation (1), page 4, defines μn,m = C(n,m)·2^{n−m}. Equation (3), page 4, defines Hn(x) = −Σᵢ pᵢ log₂(pᵢ), with pᵢ = ωx(yᵢ)/μn,m. Equation (11), page 7, defines
κ2(x) = Σ_{1≤r,s≤m} C(r+s−2,r−1)·C(2m−r−s,m−r)·[[xᵣ=xₛ]].

Binary strings are represented by functions Fin k → Bool, false for 0 and true for 1. List.ofFn reads their positions in increasing order. List.sublists keeps one entry per index subset, including repeated equal subwords. Filtering for x and taking the length therefore counts masks, rather than distinct subword values. Lean indices start at zero: the two binomial factors become C(r+s,r) and C(2m−2−r−s,m−1−r). Incompatible words have zero mass and contribute zero entropy. Dividing the finite natural-logarithm Shannon sum by Real.log 2 gives bits.

The finite ordering question is separate from the paper's asymptotic entropy minimization theorem as n tends to infinity with m fixed.
