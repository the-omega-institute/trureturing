---
bibkey: manabe2024restrictedamalgamation
authors: Hikaru Manabe
year: 2024
title: An Amalgamation Nim with Restriction
doi: 10.48550/arXiv.2411.14488
url: https://arxiv.org/abs/2411.14488v1
claim: Conjecture 1 relates both parities of the Grundy value to the same adjacent pair of XOR values in restricted three-pile amalgamation Nim.
strata_touched:
  - D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2411.14488

Source: https://arxiv.org/abs/2411.14488v1

## Game and options

Definition 4, page 2:

> Two players take turns to do one of the following (i) and (ii). (i) A player chooses a pile and removes any number of stones from the pile. (ii) A player can replace two piles with a single pile containing the total number of stones in the original two piles when the numbers of stones in two piles are equal to or more than 2.

Definition 5, pages 2–3:

> For x, y, z ∈ Z≥0, we define

The six sets printed as (1)–(6) are the three strict single-pile reductions and
the three possible pair mergers. Each merger includes both placements of
the sum and zero. The equality signs joining these sets denote their union.
The formal move definition includes exactly those six sets, with zero allowed
as a pile size. The Grundy number is the mex of the option values. The
recursion measure is the stone total plus the number of nonempty piles;
every option has smaller measure, making the recursion guard inactive.

## Conjecture 1

Section 3, page 14:

> For n ∈ Z≥0, we have the following (i) and (ii). (i) If the Grundy number of a position (x, y, z) is 2n, then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1. (ii) If the Grundy number of a position (x, y, z) is 2n + 1, then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1.

The formal claim preserves both implications for every natural pile size
and every natural n. Nat.xor denotes bitwise XOR.

## Scope and literature

The exact formula derived in the repository is 2h + (p XOR δ): h is the XOR
of the half-pile quotients, p the XOR of their remainders, and δ indicates
the existence of a positive disjoint quotient pair without all three
quotients being positive and pairwise disjoint. This implies Conjecture 1.
The entire Definition 6 P-set equivalence has only numerical evidence here.
Four or more piles and unrestricted amalgamation Nim remain open.

The source and literature screen are recorded at
https://github.com/the-omega-institute/trureturing/issues/19861.
The arXiv history lists v1; the CGTC V abstract still states a conjecture.
Later Manabe articles were keyword-screened, without a systematic audit of
implicit general theorems. Citation-service coverage and unread references
leave completeness ASSUMED-UNVERIFIED. No publication-priority claim is made.

The independent finite experiment is in
the-omega-institute/trureturing-experiments, commit ffbf16ab,
docs/reports/manabe-2024-restricted-amalgamation-nim-conjecture-1/check.py,
SHA-256 9fe9d0293073584a03f7249591ae254519e12932685709745b6a2d2f5dab30c4.
The recorded run exits 0 on 68,921 positions with each pile at most 40;
it reports no mismatch for the conjecture, exact formula or Theorem 2.
The output SHA-256 is ed2dc754154a5a61b65044dab6e538b5856d79833e34d863538b2cf5dfce8d12.
