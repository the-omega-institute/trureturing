---
bibkey: mehat2026eulermagic
authors: Sanjit Singh Mehat
year: 2026
title: Tensor constructions for Euler magic matrices and proper examples of orders 9, 27, 81 and 243
doi: null
url: https://arxiv.org/html/2609.05530v1
claim: "Problem 9.2 asks for arbitrary finite families of order-three integer orthogonality factors with distinct indexed square products; Problem 9.1 asks for proper Euler magic matrices of every order 3^k, k >= 2."
strata_touched:
  - D5/S3/Arith/Mehat/OrthogonalityProducts
license: citation-only
triage: anchor
---

# Euler magic matrices and orthogonality factors

## Verified locator

Primary source: https://arxiv.org/html/2609.05530v1.
Section 9, Problem 9.2 is at `S9.Thmtheorem2` and asks for order-three
orthogonality factors for every finite length with all indexed products of
entry squares pairwise distinct. Definition 2.1 at `S2.Thmtheorem1` defines
an integer orthogonality factor by `A A^T = gamma I` with nonzero integer
`gamma`. Lemma 2.4 at `S2.Thmtheorem4`, equation (4) at `S2.E4`, gives the
nine-entry quaternion matrix and its squared-norm orthogonality constant.
This citation-only note identifies the problem and classical construction;
the answer proved in this repository is repository-derived, not attributed
to the cited paper.

## Scope

The primary source is arXiv:2609.05530v1, Section 9, Problems 9.2 and 9.1.
Definition 2.1 and Lemma 2.4 give the integer orthogonality-factor condition
and the quaternion rotation formula. Definitions 1.1 and 3.1, Corollary 3.11,
Lemma 3.12 and Proposition 6.1 specify the Euler diagonal equations and
properness needed for the dependent matrix-existence question.

The factor argument avoids finitely many nonzero collision polynomials at an
integer point. It does not require multiplicative separation of magnitudes.
Its Lean theorem treats every positive length and every indexed entry choice.
The full same-matrix transfer to both Euler diagonals is a separate obligation.

The author's published Lean sources are pinned at
https://github.com/Bome2017/run004-euler-magic-verification/tree/b9b4821f2078fcd75c7786e760f336c7688ced30.
Their toolchain and Mathlib revision differ from this project's pins.
No published Lean source is transplanted into this module.

The named source and repository checks do not establish worldwide novelty;
unavailable citing, related-paper and general-search checks remain incomplete.
