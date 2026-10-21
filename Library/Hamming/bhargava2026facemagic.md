---
bibkey: bhargava2026facemagic
authors: Manjul Bhargava
year: 2026
title: "The existence and uniqueness of magic-faced hypercubes, and applications to Khajuraho most-perfect magic squares, cubes, and hypercubes"
doi: null
url: https://arxiv.org/html/2609.26762v1
claim: "Section 6.2 asks for the unrestricted face-magic hypercube module in even positive characteristic and for real even-subset-sum collisions."
strata_touched:
  - D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule
  - D5/S3/Combinatorics/SubsetSpectrum/RealClassification
license: citation-only
triage: anchor
---

# Bhargava face-magic hypercubes

Manjul Bhargava, *The existence and uniqueness of magic-faced hypercubes, and applications to Khajuraho most-perfect magic squares, cubes, and hypercubes*, arXiv:2609.26762v1 (22 September 2026), §6.2, https://arxiv.org/html/2609.26762v1#S6.SS2.

The source asks: **What is the structure of the R-module U_n(R) of face magic hypercubes of dimension n over R when the characteristic is even and positive?** Its unrestricted arrays are functions on all subsets of `{1,…,n}` for which every two-coordinate face has one common sum. The formal source answers this over every unital ring: dimensions zero and one have coordinates `R` and `R × R`, while dimensions at least two have the empty entry, the singleton entries, and the common face sum.

## Verified locator

URL: https://arxiv.org/html/2609.26762v1

Section 2 defines the common face sum in equation (4) and develops the face recurrence and induction in equations (8), (9) and Theorem 13. Its determinant-two coordinates motivate the distinction from the integral empty-entry, singleton-entry and common-face-sum coordinates used here.

Section 6.2, https://arxiv.org/html/2609.26762v1#S6.SS2, asks the quoted module-structure question in even positive characteristic. The question concerns unrestricted entries, rather than a prescribed set of labels.

## Real even-subset spectra

Section 6.2 also asks whether the collisions in Example 25, over characteristic
17, can occur over the reals, and whether the analogues of Lemmas 16 and 17 hold
for achievable real label collections. The even-dimensional coefficient portion
has the following precise structural answer. For odd `m ≥ 3`, the multisets of
even-cardinality subset sums of two real families of length `m` agree exactly
when a permutation of the coefficient occurrences and a sign reversal on an
even-cardinality zero-sum index set carry one family to the other. Zeros and
repetitions are allowed.

The theorem `real_even_spectrum_classification` in `SubsetSpectrum/RealClassification`
proves this coefficient statement. Its full-spectrum predecessor is attributed separately to Ciprietti
and Glaudo. The result does not assert the odd-dimensional Lemma 17 analogue or
identify the group denoted `W(B_n)` in the source, and does not settle all of the
source's real-label questions.
