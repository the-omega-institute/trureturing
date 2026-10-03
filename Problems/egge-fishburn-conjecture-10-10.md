---
slug: egge-fishburn-conjecture-10-10
bibkey: egge2022pattern
doi: 10.48550/arXiv.2208.01484
url: https://arxiv.org/abs/2208.01484v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Fishburn/FishburnTenTen.result
---

# Fishburn Permutations Avoiding 2143, 1423 and 3124

## Problem

Eric S. Egge, *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*, arXiv:2208.01484v1, Section 10:

> Conjecture 10.10. For all n ≥ 0, |Fn(2143, 1423, 3124)| = |Sn(321, 2143, 3124)| = |Sn(231, 4132, 2134)|.

A permutation p is Fishburn when there are no indices i and j > i + 1 with p_i = p_j + 1 < p_{i+1}; F_n(B)
and S_n(B) are the Fishburn permutations and all permutations of length n avoiding the classical patterns
in B.

## Motivation

The theorem `D5/S3/Combinatorics/Fishburn/FishburnTenTen.result` establishes the statement: the three
classes are equinumerous for every n ≥ 0; each has one element for n = 0 and n + 2·C(n, 3) elements for
n ≥ 1.

## Gap

Pre-registration issue 12022 records the literature screen: of the papers citing arXiv:2208.01484,
only Du and Zhang settle conjectures of the paper (Conjectures 10.14 and 10.17), and none of the located
later papers treats this one. This is a bounded negative finding.

## Route

1. Inserting a new maximum into a Fishburn permutation keeps it Fishburn exactly at the far left or right
   after an entry x with x = 1 or x − 1 to its left; deleting the maximum is the parent operation for all
   three classes.
2. The active insertion slots are characterized exactly for each class.
3. The Fishburn class splits into six explicit forms with a complete generating tree and its count.
4. Each classical class has its own generating tree, with universal transition formulas for internal and
   final insertion and an explicit type classification, giving the same count.

## Falsifier

The statement would fail if some active slot were misclassified, if a parent produced a child twice or
missed one, or if the three counts differed for some length.

## Evidence

Every structural lemma, transition and type count was checked on all permutations of length at most 12;
the common counts for n = 0, …, 12 are 1, 1, 2, 5, 12, 25, 46, 77, 120, 177, 250, 341, 452.

## Triage

`theorem`; the statement is a conjecture of Section 10 of arXiv:2208.01484 and is quantified over every n.

The Fishburn side of the theorem also decides Conjecture 10.6 of the same paper, which concerns the same
class F_n(2143, 1423, 3124). As printed, Conjecture 10.6 asserts the count 2·C(n + 1, 3) + n + 1 for
n ≥ 1; this is false at every n ≥ 1, since the class has n + 2·C(n, 3) elements (already 1 ≠ 2 at
n = 1). The printed expression equals the proved count at n + 1, so the intended statement is the proved
one with the index shifted by one (proved). Conjectures 10.7 and 10.8 concern different classes and are
not affected.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, the arXiv and GitHub searches and the repository
checks recorded above.
