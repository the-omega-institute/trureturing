---
slug: egge-fishburn-conjecture-10-9
bibkey: egge2022pattern
doi: 10.48550/arXiv.2208.01484
url: https://arxiv.org/abs/2208.01484v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Fishburn/FishburnTenNine.result
---

# Fishburn Permutations Avoiding 2143 and 3124

## Problem

Eric S. Egge, *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*, arXiv:2208.01484v1, Section 10:

> Conjecture 10.9. For all n ≥ 1, |Fn(2143, 3124)| = |Sn(231, 4123)|.

A permutation p is Fishburn when there are no indices i and j > i + 1 with p_i = p_j + 1 < p_{i+1}; F_n(B)
and S_n(B) are the Fishburn permutations and all permutations of length n avoiding the classical patterns
in B.

## Motivation

The theorem `D5/S3/Combinatorics/Fishburn/FishburnTenNine.result` establishes the statement: the two classes are equinumerous for every n ≥ 1; both have the generating function (1 − x)^3/(1 − 4x + 5x^2 − 3x^3).

## Gap

Pre-registration issue 11829 records the literature screen: of the papers citing arXiv:2208.01484,
only Du and Zhang settle conjectures of the paper (Conjectures 10.14 and 10.17), and none of the located
later papers treats this one. This is a bounded negative finding.

## Route

1. The active sites of a Fishburn permutation avoiding 2143 and 3124 are characterized completely through its prefix, using layered permutations as an auxiliary class.
2. This gives a complete generating tree for the Fishburn class with explicit inverse, and its count.
3. A separate maximum decomposition of the permutations avoiding 231 and 4123 gives the same generating function.

## Falsifier

The statement would fail if some active insertion site were misclassified, if a parent produced a child
twice or missed one, or if the two counts differed for some length.

## Evidence

Every structural lemma was checked on all permutations of length at most 10; the counts agree through the
lengths reported in the pre-registration.

## Triage

`theorem`; the statement is a conjecture of Section 10 of arXiv:2208.01484 and is quantified over every n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, the arXiv and GitHub searches and the repository
checks recorded above.
