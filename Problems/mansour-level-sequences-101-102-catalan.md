---
slug: mansour-level-sequences-101-102-catalan
bibkey: mansour2026wilf
doi: 10.3390/math14111983
url: https://www.mdpi.com/2227-7390/14/11/1983
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/LevelSequence/LevelSequenceCatalan.result
---

# Level Sequences Avoiding 101 and 102

## Problem

Toufik Mansour, *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*, Mathematics 14(11),
1983 (2026), Section 4:

> Problem 1. We have that F_{101,102}(x) = (1 − √(1 − 4x))/(2x) − 1.

A level sequence of length n is a sequence w_1 ⋯ w_n of nonnegative integers with w_1 = 0 and
w_i ≤ 1 + lev(w_1 ⋯ w_{i−1}), where lev counts adjacent equal entries; the problem asks for the number of
level sequences avoiding the patterns 101 and 102.

## Motivation

The theorem `D5/S3/Combinatorics/LevelSequence/LevelSequenceCatalan.result` establishes the statement: for
every n ≥ 1 the number of level sequences of length n avoiding 101 and 102 is the Catalan number C_n.

## Gap

Pre-registration issue 12044 records the literature screen: the citation index records no citing work, and
the arXiv, OEIS and GitHub searches located no later treatment of the problem. This is a bounded negative
finding.

## Route

1. A word avoids 101 and 102 exactly when every descent is permanent: after w_i > w_j with i < j, every
   later
   entry is smaller than w_i.
2. Words over a k-letter alphabet with this property decompose at the first letter into an upper block and a
   lower word, which gives a convolution recurrence for their counts f_k.
3. A level sequence avoiding 101 and 102 splits uniquely into its maximal weakly increasing prefix and a
   descending sequence of value bands; each band is an arbitrary avoiding word over its interval of values.
4. The level bound becomes a slack variable on the prefix, and the resulting succession rule is solved by
   the
   kernel method; the kernel root satisfies (2 + x)Z^2 − (1 + 2x)Z + x = 0, which yields the Catalan series.

## Falsifier

The statement would fail if the prefix-and-band decomposition missed or repeated a sequence, if a band could
contain a value outside its interval, or if the slack recursion admitted a step that violates the level
bound.

## Evidence

Every lemma, the decomposition in both directions, the slack recursion and the series identities were
checked on all level sequences of length at most 11; the counts agree with the Catalan numbers through
n = 15.

## Triage

`theorem`; the statement is the open Problem 1 of the source and is quantified over every n ≥ 1.

The same strong-descent description shows that, over any fixed alphabet [k], the words avoiding 101 and 102
are counted by the recurrence f_k = 1 + x Σ_{a=1}^{k} f_{k−a+1} f_{a−1} with the explicit bivariate
generating
function obtained in the proof (proved). Whether the slack decomposition gives closed forms for the other
pairs and triples of length-three patterns that the source treats only through multiple sums was not
examined (open).

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation index, arXiv, OEIS and GitHub searches and the repository
checks recorded above; the publisher full text was read through ResearchGate, not directly.
