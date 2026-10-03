---
slug: franklin-indecomposable-321-1342-count
bibkey: franklin2024inversions
doi: 10.48550/arXiv.2410.07467
url: https://arxiv.org/abs/2410.07467v4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.result
  - D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.avoiders_ncard
---

# The Number of Indecomposable 321- and 1342-Avoiders with k Inversions

## Problem

Atli Fannar Franklín, *Pattern avoiding permutations enumerated by inversions*, arXiv:2410.07467v4, Section 1,
printed pages 2–3:

> Another case is I_k(321, 1342), which we conjecture to have k(k + 1)/2 + 1 elements.

Here I_k is the set of direct-sum indecomposable permutations, of any length, with exactly k inversions, and
I_k(321, 1342) is its subset avoiding the classical patterns 321 and 1342.

## Motivation

The theorem `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.avoiders_ncard` proves
|I_k(321, 1342)| = k(k − 1)/2 + 1 for every k ≥ 0, and `FranklinInversion.result` derives from it that the printed
formula is false.

## Gap

Pre-registration issue 12442 records the literature screen: the paper citing arXiv:2410.07467 that settles the
companion conjecture on I_k(132, 4321) (arXiv:2604.01143) does not treat I_k(321, 1342), and the GitHub and
repository searches located no treatment. This is a bounded negative finding.

## Route

1. Every member of I_k(321, 1342) is either a star of length k + 1 or a five-block permutation B(r, t, d, h) with
   explicit parameter ranges; the two families are disjoint and the parametrization is injective.
2. Stars have k = n − 1 inversions, and B(r, t, d, h) has rt + d + h inversions.
3. Euclidean division matches the five-block members with k inversions to the pairs 1 ≤ t < q ≤ k, giving
   k(k − 1)/2 of them, plus one star.

## Falsifier

The statement would fail if a member of I_k(321, 1342) had neither form, if two parameter tuples gave the same
permutation, or if an inversion formula were wrong.

## Evidence

The classification, the inversion formulas and the counts were checked on all 321-avoiders with at most 14
inversions; the counts for k = 0, …, 14 are 1, 1, 2, 4, 7, 11, 16, 22, 29, 37, 46, 56, 67, 79, 92. An independent
referee implementation confirmed every lemma through k = 12.

## Triage

`theorem`; the printed conjecture of Section 1 of arXiv:2410.07467 is refuted, and the corrected count is proved
for every k.

- Proved (formalized): |I_k(321, 1342)| = k(k − 1)/2 + 1 for every k ≥ 0; the printed formula is the count of
  I_{k+1}(321, 1342), an index shift.
- Open: the exact enumeration of the indecomposable permutations of length n avoiding 321 and 1342 (the source
  reports experimental growth like n³/6), and the asymptotic bound the source derives from the printed formula, which
  has to be re-derived from the corrected count.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citing papers, the arXiv and GitHub searches and the repository checks
recorded above; the journal version was not compared with arXiv v4.
