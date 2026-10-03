---
slug: egge-fishburn-conjecture-10-13
bibkey: egge2022pattern
doi: 10.48550/arXiv.2208.01484
url: https://arxiv.org/abs/2208.01484v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen.result
---

# Fishburn Permutations Avoiding 2413 and 2431, or 2431 and 3241

## Problem

Eric S. Egge, *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*, arXiv:2208.01484v1, Section 10:

> Conjecture 10.13. For all n ≥ 1, |Fn(2413, 2431)| = |Fn(2431, 3241)| = Σ_{k=1}^{n} C(n−1, k−1) C_{n−k}.

Here C_m is the m-th Catalan number. A permutation p is Fishburn when there are no indices i and j > i + 1
with p_i = p_j + 1 < p_{i+1}; F_n(B) is the set of Fishburn permutations of length n avoiding the classical
patterns in B.

## Motivation

The theorem `D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteen.result` establishes the statement:
both classes have Σ_{k=1}^{n} C(n − 1, k − 1) C_{n−k} elements of length n for every n ≥ 1, the binomial
transform of the Catalan numbers (OEIS A007317).

## Gap

Pre-registration issue 12021 records the literature screen: of the papers citing arXiv:2208.01484,
only Du and Zhang settle conjectures of the paper (Conjectures 10.14 and 10.17), and none of the located
later papers treats this one. This is a bounded negative finding.

## Route

1. A permutation in either class decomposes uniquely as a direct sum of indecomposable components, each in
   the same class, so the generating function is F = 1/(1 − F_ind).
2. For each class separately, the indecomposable members are described by a reversible construction.
3. With t = x/(1 − x) and the Catalan series C, both classes satisfy F(x) = 1 + t C(t), whose coefficients
   are the stated binomial transform.

## Falsifier

The statement would fail if the direct-sum decomposition were not unique, if an indecomposable member were
missed or produced twice by the construction, or if the two counts differed for some length.

## Evidence

Every structural lemma, both reversible decompositions and the formal series identities were checked on
all permutations of length at most 11; the counts agree through n = 12.

## Triage

`theorem`; the statement is a conjecture of Section 10 of arXiv:2208.01484 and is quantified over every
n ≥ 1.

- Proved (formalized): both classes have the generating function F(x) = 1 + t C(t) with t = x/(1 − x).
- Proved (paper argument, not formalized): by the source's Lemma 10.15, F = 1/(1 − F_ind), so the
  indecomposable members of both classes have the generating function 1 − 1/(1 + t C(t)), the binomial
  transform of Fine's sequence (OEIS A033321). The source states that Conjectures 10.13 and 10.16 are
  equivalent in view of Lemma 10.15; Conjecture 10.16 additionally identifies these counts with
  |S_{n−1}(2413, 3412, 2143)|, whose enumeration by A033321 is taken from the source and not re-proved here.
- Open: the source's remark that the common refinement |F_n^ind(2413, 2431, 3241)| is given by OEIS A078482
  is not addressed by this result.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, the arXiv and GitHub searches and the repository
checks recorded above.
