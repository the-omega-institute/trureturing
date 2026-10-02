---
slug: egge-fishburn-conjecture-10-7
bibkey: egge2022pattern
doi: 10.48550/arXiv.2208.01484
url: https://arxiv.org/abs/2208.01484v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSeven.result
---

# Fishburn Permutations Avoiding Three Patterns from {1324, 2143, 1423, 3124}

## Problem

Eric S. Egge, *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*, arXiv:2208.01484v1, Section 10:

> Conjecture 10.7. For all n ≥ 1, |Fn(1324, 2143, 1423)| = |Fn(1324, 2143, 3124)| = |Fn(1324, 1423, 3124)|
> = 2^n − n.

A permutation p is Fishburn when there are no indices i and j > i + 1 with p_i = p_j + 1 < p_{i+1}; F_n(B)
is the set of Fishburn permutations of length n avoiding the classical patterns in B. The source notes that
2^n − n also counts the Grassmannian permutations of length n.

## Motivation

The theorem `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSeven.result` establishes the statement: each of
the three classes has 2^n − n elements of length n for every n ≥ 1.

## Gap

Pre-registration issue 12116 records the literature screen: of the papers citing arXiv:2208.01484,
only Du and Zhang settle conjectures of the paper (Conjectures 10.14 and 10.17), and none of the located
later papers treats this one. This is a bounded negative finding.

## Route

1. A Fishburn permutation avoiding 1324 and 1423 has the unique shape D 1 I m J, with D decreasing, I
   increasing, m the largest entry from 1 on and J decreasing; it is Fishburn exactly when no t in J has t + 1
   in I.
2. Besides the decreasing permutation, the first class consists of the shapes with J < D, and the third of
   the shapes in which every entry of D below m is smaller than every entry of I; both are encoded by words in
   three letters, and reversing a word while interchanging I and J is a bijection between the two languages.
3. The second class has its own reversible normal forms, built from an auxiliary Fishburn class avoiding 213.
4. Counting the words and the normal forms gives 2^n − n for each class.

## Falsifier

The statement would fail if some member of a class had no shape or two shapes, if the word encoding were not
reversible, or if a normal form of the second class were missed or produced twice.

## Evidence

Every structural assertion, the encodings and the normal forms were checked on all permutations of length at
most 11; the three counts agree with 2^n − n through n = 11.

## Triage

`theorem`; the statement is a conjecture of Section 10 of arXiv:2208.01484 and is quantified over every
n ≥ 1.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, the arXiv and GitHub searches and the repository
checks recorded above.
