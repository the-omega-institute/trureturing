---
slug: egge-fishburn-conjecture-10-5
bibkey: egge2022pattern
doi: 10.48550/arXiv.2208.01484
url: https://arxiv.org/abs/2208.01484v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Fishburn/FishburnTenFive.result
---

# Fishburn Permutations Avoiding Pairs Counted by Odd-Indexed Fibonacci Numbers

## Problem

Eric S. Egge, *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*, arXiv:2208.01484v1, Section 10:

> Conjecture 10.5. For all n ≥ 1, |Fn(1324, 1423)| = |Fn(1324, 3124)| = F_{2n−2}.

A permutation p is Fishburn when there are no indices i and j > i + 1 with p_i = p_j + 1 < p_{i+1}; F_n(B)
and S_n(B) are the Fishburn permutations and all permutations of length n avoiding the classical patterns
in B.

## Motivation

The theorem `D5/S3/Combinatorics/Fishburn/FishburnTenFive.result` establishes the statement: both classes have F_{2n−2} elements of length n ≥ 1 in the source indexing F_0 = F_1 = 1, which is Nat.fib (2n − 1).

## Gap

Pre-registration issue 11816 records the literature screen: of the papers citing arXiv:2208.01484,
only Du and Zhang settle conjectures of the paper (Conjectures 10.14 and 10.17), and none of the located
later papers treats this one. This is a bounded negative finding.

## Route

1. Inserting the maximum and deleting it are inverse operations on Fishburn permutations; the active gaps of a permutation are given by exact local tests, and a gap that becomes inactive never recovers.
2. For each class an invariant describes all active sites, and the site updates under insertion give a labelled succession rule.
3. Counting paths in the two succession rules gives coupled two-state recurrences whose solution is the odd-indexed Fibonacci numbers.

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
