---
slug: egge-fishburn-conjecture-10-4
bibkey: egge2022pattern
doi: 10.48550/arXiv.2208.01484
url: https://arxiv.org/abs/2208.01484v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Fishburn/FishburnTenFour.result
---

# Fishburn Permutations Avoiding Pairs Counted by (n − 1)2^(n−2) + 1

## Problem

Eric S. Egge, *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*, arXiv:2208.01484v1, Section 10:

> Conjecture 10.4. For all n ≥ 1, |Fn(1324, 2143)| = |Fn(1423, 2143)| = |Fn(1423, 3124)| = (n − 1)2^{n−2} + 1.

A permutation p is Fishburn when there are no indices i and j > i + 1 with p_i = p_j + 1 < p_{i+1}; F_n(B)
and S_n(B) are the Fishburn permutations and all permutations of length n avoiding the classical patterns
in B.

## Motivation

The theorem `D5/S3/Combinatorics/Fishburn/FishburnTenFour.result` establishes the statement: each of the three classes has (n − 1)2^{n−2} + 1 elements of length n ≥ 1 (one element at n = 1).

## Gap

Pre-registration issue 11814 records the literature screen: of the papers citing arXiv:2208.01484,
only Du and Zhang settle conjectures of the paper (Conjectures 10.14 and 10.17), and none of the located
later papers treats this one. This is a bounded negative finding.

## Route

1. Inserting a new maximum right after an entry x keeps a Fishburn permutation Fishburn exactly when x = 1 or x − 1 lies to the left of x; insertion at the far left is always allowed, and deleting the maximum keeps the Fishburn condition.
2. For each of the three classes the active insertion sites are described exactly by pattern guards, and the guards are transported along the insertion of the maximum.
3. This gives three explicitly reversible generating trees, one per class, whose level counts satisfy d_{n+1} = 2d_n + 2^{n−1} with d_n = a_n − 1.

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
