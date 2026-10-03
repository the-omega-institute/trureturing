---
slug: egge-fishburn-conjecture-10-11
bibkey: egge2022pattern
doi: 10.48550/arXiv.2208.01484
url: https://arxiv.org/abs/2208.01484v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Fishburn/FishburnTenEleven.result
---

# Fishburn Permutations Avoiding 1243 and 2134

## Problem

Eric S. Egge, *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*, arXiv:2208.01484v1, Section 10:

> Conjecture 10.11. For all n ≥ 0, |Fn(1243, 2134)| = |Sn(123, 3241)|.

A permutation p is Fishburn when there are no indices i and j > i + 1 with p_i = p_j + 1 < p_{i+1}; F_n(B)
and S_n(B) are the Fishburn permutations and all permutations of length n avoiding the classical patterns
in B.

## Motivation

The theorem `D5/S3/Combinatorics/Fishburn/FishburnTenEleven.result` establishes the statement: the two classes are equinumerous for every n; both have 3·2^{n−1} − binom(n+1, 2) − 1 elements of length n ≥ 1.

## Gap

Pre-registration issue 11828 records the literature screen: of the papers citing arXiv:2208.01484,
only Du and Zhang settle conjectures of the paper (Conjectures 10.14 and 10.17), and none of the located
later papers treats this one. This is a bounded negative finding.

## Route

1. On both sides every nonempty permutation has two ordinary maximum-insertion children.
2. The parents with one additional child form an explicitly described family in bijection with the two-element subsets of [n], on each side separately.
3. Both classes therefore satisfy a_{n+1} = 2a_n + binom(n, 2) for n ≥ 1 with the same initial values.

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
