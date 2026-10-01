---
slug: archer-laudone-theta-cube-231-312
bibkey: archer2024fundamental
doi: 10.48550/arXiv.2407.06338
url: https://arxiv.org/abs/2407.06338v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/FundamentalBijection/ThetaCube.result
---

# Avoiders of 231 and 312 Fixed by the Third Iterate of the Fundamental Bijection

## Problem

Kassie Archer and Robert P. Laudone, *Pattern avoidance and the fundamental bijection*,
arXiv:2407.06338v1, Section 5, Conjecture 5.6:

> For σ ∈ {231, 312}, the generating functions F_σ^k(x) are rational. A few examples of conjectured
> generating functions for these patterns are found below. F_σ^3(x) = 1/(1 − x − x^2 − 2x^3)

Here F_σ^k(x) = Σ f_n^k(σ) x^n and f_n^k(σ) counts the permutations of [n] avoiding σ and fixed by the
k-th iterate of the fundamental bijection θ.

## Motivation

The theorem `D5/S3/Combinatorics/FundamentalBijection/ThetaCube.result` establishes
F_σ^3(x) (1 − x − x^2 − 2x^3) = 1 for both σ = 231 and σ = 312, so f_n^3(σ) = 1, 1, 2, 5, 9, 18, 37, 73,
146, 293, … for n = 0, 1, ….

## Gap

Pre-registration issue 11298 records the literature screen: none of the papers citing arXiv:2407.06338
treats this conjecture, and the journal version still states it. This is a bounded negative finding.

## Route

1. θ commutes with direct sums, and every 231- or 312-avoider is uniquely a direct sum of
   sum-indecomposable ones, so F_σ^3 = 1/(1 − I_σ^3) where I_σ^3 counts the indecomposable avoiders
   fixed by θ^3.
2. The inverse of θ cuts a word before each left-to-right maximum and closes each block into a cycle.
   Following the rows p, θ^{-1}(p), θ^{-2}(p) of a θ^3-fixed indecomposable avoider of size n > 3, the
   successor equations force two different entries into one position.
3. Hence the indecomposable fixed avoiders are 1, 21 and two blocks of size three, and I_σ^3 = x + x^2 + 2x^3.

## Falsifier

The statement would fail if some σ-avoider of size at least four, not a direct sum, were fixed by θ^3.

## Evidence

The successor chase was checked on every indecomposable 231- and 312-avoider of size at most 11; the
counts agree through n = 11.

## Triage

`theorem`; the formula is stated in Conjecture 5.6 of arXiv:2407.06338 and is quantified over every n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, arXiv searches and repository checks recorded
above.
