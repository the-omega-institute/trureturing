---
bibkey: fernandes2026twogeneration
authors: Vítor H. Fernandes
year: 2026
title: "Groups of permutations that are even on maximal proper subsets, and related monoids"
doi: null
url: https://arxiv.org/abs/2605.12342
claim: "Conjecture 1: for all integers m >= n >= 2 such that (m,n) is not in {(2,2), (3,3), (4,3), (4,4)}, the group Gamma_{m+n} = {(s1,s2) in S_m x S_n : sgn(s1) = sgn(s2)} has rank 2."
strata_touched:
  - D5/S3/Factorization/Galois/FernandesTwoGeneration
license: citation-only
triage: anchor
---

# Fernandes, two-generation of equal-sign permutation pairs

The claim field quotes the paper's Conjecture 1. What is settled here is a proper part of it:
two-generation holds for the whole family with second degree `n = 2` and `m >= 2`. The general
case `m >= n >= 3` outside the stated exceptions is not proved here and remains open.

The paper's exceptional set records known ranks: `rank Gamma(2,2) = 1`, and
`rank Gamma(3,3) = rank Gamma(4,3) = rank Gamma(4,4) = 3`. Those values are quoted from the
paper and are not reproved in this repository.

`Gamma(m,n)` is realised as the kernel of the sign-difference homomorphism
`(s1, s2) |-> sgn(s1) * sgn(s2)^{-1}` into the units of the integers, which makes it an
index-two subgroup of the product containing `A_m x A_n`.

Formalisation note: the conjecture is carried as an open statement in the Formal Conjectures
corpus at `FormalConjectures/Arxiv/2605.12342/Conjecture1.lean`. That corpus was consulted for
deduplication only; nothing from it is imported.
