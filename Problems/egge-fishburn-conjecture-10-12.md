---
slug: egge-fishburn-conjecture-10-12
bibkey: egge2022pattern
doi: 10.48550/arXiv.2208.01484
url: https://arxiv.org/abs/2208.01484v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Fishburn/FishburnTenTwelve.result
---

# Fishburn Permutations Avoiding 1243 and 3124

## Problem

Eric S. Egge, *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*, arXiv:2208.01484v1, Section 10:

> Conjecture 10.12. For all n ≥ 0, |Fn(1243, 3124)| = |Sn(231, 4123)|.

A permutation p is Fishburn when there are no indices i and j > i + 1 with p_i = p_j + 1 < p_{i+1}; F_n(B)
and S_n(B) are the Fishburn permutations and all permutations of length n avoiding the classical patterns
in B.

## Motivation

The theorem `D5/S3/Combinatorics/Fishburn/FishburnTenTwelve.result` establishes the statement: the two classes are equinumerous for every n.

## Gap

Pre-registration issue 11830 records the literature screen: of the papers citing arXiv:2208.01484,
only Du and Zhang settle conjectures of the paper (Conjectures 10.14 and 10.17), and none of the located
later papers treats this one. This is a bounded negative finding.

## Route

1. The active sites of a Fishburn permutation avoiding 1243 and 3124 are described exactly, together with their evolution under insertion of the maximum, which gives a four-state generating tree.
2. The permutations avoiding 231 and 4123 decompose at their maximum, with the auxiliary class of permutations avoiding 231 and 123 described in canonical forms.
3. Paths with nonzero sites in the Fishburn tree correspond to the blocks of this decomposition, so both sides have the same counts.

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
