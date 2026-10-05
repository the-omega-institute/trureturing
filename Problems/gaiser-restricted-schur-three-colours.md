---
slug: gaiser-restricted-schur-three-colours
bibkey: gaiser2026restrictedschur
doi: 10.48550/arXiv.2608.08789
url: https://arxiv.org/abs/2608.08789v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.result
---

# The Three-Colour Restricted Schur Number S_3(k; 2) Exceeds k^3 + 3k^2 + k − 1

## Problem

Collier Gaiser, *Restricted generalized Schur numbers*, arXiv:2608.08789v1, Section 6: S_r(k; l) is the least n such
that every r-colouring of {1, …, n} has a monochromatic solution of x_1 + ⋯ + x_k = x_{k+1} with exactly l + 1
distinct integers. Proposition 6.1 proves S_3(k; 2) ≥ k^3 + 3k^2 + k − 1, and "Open Question 6.2. Is it true that
S_3(k; 2) = k^3 + 3k^2 + k − 1 for all large enough k?"

## Motivation

The theorem `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur.result` answers Open Question 6.2 negatively: for
every k ≥ 3 a seven-block 3-colouring of {1, …, k^3 + 3k^2 + 2k − 3} has no monochromatic solution with exactly
three distinct integers, so S_3(k; 2) ≥ k^3 + 3k^2 + 2k − 2.

## Gap

Pre-registration issue 13213 records the literature screen: the paper is the only source of the question, and no
later work on it was found in the repository or in web and arXiv searches.

## Route

1. A solution with exactly three distinct integers uses two distinct summand values a < b, j and k − j times with
   1 ≤ j < k, and the sum ja + (k − j)b.
2. The colouring of Proposition 6.1 is extended by a red block [k^3 + 3k^2 + k − 1, k^3 + 3k^2 + 2k − 3]; its blocks
   are A = [1, k] red, B = [k + 1, k^2 + k] blue, C = [k^2 + k + 1, k^2 + 2k − 1] red, D = [k^2 + 2k, k^3 + 2k^2]
   green, E = [k^3 + 2k^2 + 1, k^3 + 2k^2 + k − 1] red, F = [k^3 + 2k^2 + k, k^3 + 3k^2 + k − 2] blue and the new
   red block H.
3. For each pair of same-coloured blocks, interval estimates on ja + (k − j)b show that every such sum lies in a block
   of another colour or beyond the end of the interval.

## Falsifier

The theorem would fail if some colour class of the seven-block colouring contained a < b and 1 ≤ j < k with
ja + (k − j)b in the same class.

## Evidence

An exact SAT computation (CaDiCaL; one variable per integer and colour, at least one colour per integer, the colour
of 1 fixed, and a clause forbidding each monochromatic triple a < b, ja + (k − j)b for every 1 ≤ j < k with the sum
at most n) gives S_3(k; 2) = k^3 + 3k^2 + 2k − 2 for k = 3, …, 9, so the lower bound is attained there; for k = 2 it
gives 24. An independent referee implementation confirmed the colouring for k = 3, …, 40 and the exact value for
k = 3, 4, 5.

## Triage

`theorem`; the statement is Open Question 6.2 of arXiv:2608.08789v1, answered negatively.

- Refuted (formalized): S_3(k; 2) ≠ k^3 + 3k^2 + k − 1 for every k ≥ 3, by the lower bound
  S_3(k; 2) ≥ k^3 + 3k^2 + 2k − 2.
- Computed: S_3(k; 2) = k^3 + 3k^2 + 2k − 2 for 3 ≤ k ≤ 9.
- Open: whether S_3(k; 2) = k^3 + 3k^2 + 2k − 2 for every k ≥ 3; the upper bound is proved only for colourings with
  the seven-block template.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record of arXiv:2608.08789, web, arXiv and GitHub searches and the
repository checks.
