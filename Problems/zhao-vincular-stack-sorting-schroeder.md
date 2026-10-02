---
slug: zhao-vincular-stack-sorting-schroeder
bibkey: zhao2024vincular
doi: 10.1016/j.disc.2025.114834
url: https://arxiv.org/abs/2410.17057v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/VincularStack/VincularStackSort.result
---

# Schröder Enumeration of the Sorting Class of the Stack Avoiding 23-1

## Problem

Zhao, arXiv:2410.17057v1, Conjecture 3.30 (Section 3.2, printed page 11):

> The sorting class of SC_{23̲1} is enumerated by |Sort_n(SC_{23̲1})| = S_{n−1}.

SC_{23̲1} is the right-greedy stack map whose stack, read from top to bottom, must avoid the vincular pattern
23̲-1 (the entries playing 2 and 3 adjacent); Sort_n(SC_{23̲1}) is the set of permutations of length n whose
image avoids 231, and S_m is the large Schröder number.

## Motivation

The theorem `D5/S3/Combinatorics/VincularStack/VincularStackSort.result` establishes the statement: for every
n ≥ 1 the sorting class has `Nat.largeSchroder (n − 1)` elements.

## Gap

Pre-registration issue 12117 records the literature screen: the only work citing arXiv:2410.17057 concerns the
fully consecutive pattern, and the arXiv, OEIS and GitHub searches located no treatment of this conjecture.
This is a bounded negative finding.

## Route

1. The sortable permutations are characterized directly from the stack rule by avoidance of an explicit mesh
   pattern.
2. Inserting a new maximum gives a generating tree with root label 2 and succession rule
   (k) → (3)(4)⋯(k)(k + 1)(k + 1), with explicit inverse operations.
3. The rule gives the functional equation R = 1 + xR + xR^2 of the large Schröder numbers.

## Falsifier

The statement would fail if the mesh characterization missed a sortable permutation or admitted an unsortable
one, or if an insertion produced a child with the wrong label or failed to be reversible.

## Evidence

The characterization, the generating tree and its inverse were checked on all permutations of length at most
11; the counts agree with S_{n−1} through n = 11.

## Triage

`theorem`; the statement is Conjecture 3.30 of arXiv:2410.17057 and is quantified over every n ≥ 1.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation index, arXiv, OEIS and GitHub searches and the repository
checks recorded above; the journal version was not read in full.
