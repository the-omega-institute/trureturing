---
slug: cioni-ferrari-smith-pop-stack-simple
bibkey: cioni2025sorting
doi: 10.1016/j.disc.2025.114964
url: https://arxiv.org/abs/2503.08285v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PopStack/PopStackSimple.result
---

# Simple Permutations Sortable by Two Parallel Pop Stacks with Bypass

## Problem

Lapo Cioni, Luca Ferrari and Rebecca Smith, *Sorting permutations using a pop stack with a bypass*,
arXiv:2503.08285v1, Section 9.2:

> Let a_n be the number of simple permutations of size n that can be sorted by a machine consisting of two
> pop stacks in parallel where entries are allowed to bypass the pop stacks. Then a_0 = a_1 = 1, a_2 = 2,
> a_n = F_{2n−5} − 1 if n ≥ 3 is odd, and a_n = F_{2n−5} if n > 3 is even.

The sortable permutations are the class C = Av(2341, 25314, 42513, 42531, 45213, 45231, 52314, 642135,
642153); a permutation is simple when it has no interval of length strictly between 1 and n.

## Motivation

The theorem `D5/S3/Combinatorics/PopStack/PopStackSimple.result` establishes the stated values for every n:
the simple permutations of length n in C number 1, 1, 2 for n = 0, 1, 2 and F_{2n−5} − (n mod 2) for n ≥ 3.

## Gap

Pre-registration issue 11689 records the literature screen: no later paper, citing record or public
repository treats the conjecture. This is a bounded negative finding.

## Route

1. Intervals in C behave well under union, contraction and inflation; inserting a new minimum in one of
   the first three positions is characterized exactly, and a small auxiliary class of two-chain
   permutations with its simple and prefix-only members is described completely.
2. The simple permutations of C, together with one extra non-simple permutation for each odd length, are
   split by the position of their minimum: position 2, position 3, or later.
3. An explicit recursive map T with inverse and an explicit bijection Φ show that the first two parts each
   have b_{n−1} elements, and a continuation V with proved inverse shows that the third part has
   b_{n−1} − b_{n−2} elements.
4. Hence b_n = 3b_{n−1} − b_{n−2} with b_3 = 1 and b_4 = 2, so b_n = F_{2n−5}, and removing the odd
   extra permutation gives the stated formula.

## Falsifier

The statement would fail if some simple permutation of C had no place in the three-part split, if T, Φ
or V were not bijective, or if the odd extra permutation were simple.

## Evidence

Every structural lemma, the three-part split and both inverse identities of T, Φ and V were checked on all
permutations of length at most 11; the counts agree through n = 11.

## Triage

`theorem`; the statement is the conjecture of Section 9.2 of arXiv:2503.08285 and is quantified over every
n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv, citation-index, OEIS and GitHub searches and the repository
checks recorded above; the published journal version was not read in full.
