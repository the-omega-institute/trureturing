---
bibkey: burcroffwinsor2019lyndon
authors: Amanda Burcroff and Eric Winsor
year: 2019
title: "Generalized Lyndon Factorizations of Infinite Words"
doi: null
url: https://arxiv.org/abs/1905.04746v2
claim: "The introduction states that every finite word over a totally ordered, possibly infinite alphabet has a unique factorization into nonincreasing Lyndon words."
strata_touched:
  - D5/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique
license: citation-only
triage: anchor
---

# Classical finite Lyndon factorization

The introduction on PDF page 1 defines a finite Lyndon word by strict
lexicographic minimality among its nontrivial rotations. It explicitly permits
a totally ordered, possibly infinite alphabet and states the uniqueness of the
factorization of a finite word into nonincreasing Lyndon words. This is the
classical Chen–Fox–Lyndon theorem; the paper studies further generalized and
infinite-word factorizations.

The repository theorem uses the existing rotation predicate `IsLyndon` and
proves uniqueness for arbitrary lists of factors with equal concatenations.
The order condition is weak: equal adjacent factors are allowed. The alphabet
requires only a linear order. Empty factor lists and singleton factorizations
are included. Existence is separate and is not assumed in the uniqueness
statement.

The proof recovers the final factor as the least nonempty suffix of the word.
A suffix begins either inside an earlier Lyndon factor, where the proper-suffix
characterization and nonincrease give a lower bound, or inside the remaining
factorization. The two factorizations therefore have equal final factors;
right cancellation and induction recover the entire factor list. This proof
organization implements classical mathematics and carries no originality claim.

## Verified locator

The source is arXiv:1905.04746v2, PDF page 1, introduction paragraphs 1–2.
The stable versioned URL is https://arxiv.org/abs/1905.04746v2.
The original Chen–Fox–Lyndon article was not inspected; attribution here follows
the cited introduction.
