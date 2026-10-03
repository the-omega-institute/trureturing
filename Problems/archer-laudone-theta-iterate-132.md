---
slug: archer-laudone-theta-iterate-132
bibkey: archer2024fundamental
doi: 10.48550/arXiv.2407.06338
url: https://arxiv.org/abs/2407.06338v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/FundamentalBijection/ThetaIterate.result
---

# Permutations Whose First Iterates under the Fundamental Bijection Avoid 132

## Problem

Kassie Archer and Robert P. Laudone, *Pattern avoidance and the fundamental bijection*,
arXiv:2407.06338v1, Section 4, Conjecture 4.5:

> For n ≥ 2, t_n^2(132) = k^3 + 3k^2 + 2k − 1 (n = 3k), k^3 + 4k^2 + 4k (n = 3k + 1),
> k^3 + 5k^2 + 7k + 2 (n = 3k + 2). The conjectured values for k ≥ 3 are found in the table below:
> 3n − 4, 2n − 1, n + 2 and 5 for k = 3, 4, 5 and k ≥ 6.

Here t_n^k(σ) counts the permutations π of [n] such that π, θ(π), …, θ^k(π) all avoid σ.

## Motivation

The theorem `D5/S3/Combinatorics/FundamentalBijection/ThetaIterate.result` establishes the cubic
quasipolynomial for t_n^2(132) for every n ≥ 2, and t_n^3(132) = 3n − 4, t_n^4(132) = 2n − 1,
t_n^5(132) = n + 2 and t_n^k(132) = 5 for every k ≥ 6, for every n ≥ 3. The table does not state where
its rows start; they hold from n = 3, and t_1^k = 1, t_2^k = 2.

## Gap

Pre-registration issue 11324 records the literature screen: none of the papers citing arXiv:2407.06338
treats this conjecture, and the paper describes the case of 132 as complicated. This is a bounded
negative finding.

## Route

1. A 132-avoider splits at its maximum into a larger left part and a smaller right part; cutting a word
   before its left-to-right maxima gives a block criterion for 132-avoidance and the inverse of θ.
2. Appending the maximum as a fixed point preserves every layer, so it suffices to classify the members
   of each layer that do not end with n: a scan through the blocks of r, θ(r) and a companion word ρ(r)
   parametrizes them, and summing gives the quasipolynomial.
3. Three explicit words E_n → D_n → C_n leave the layers one at a time, and the five permutations
   obtained from 123, 213, 231, 312, 321 by appending 4, …, n form a θ-invariant set, which gives the
   higher layers.

## Falsifier

The statement would fail if some n had a layer count different from the displayed values.

## Evidence

Exhaustive computation through n = 13 agrees with every layer count and with each classification step.

## Triage

`theorem`; the formulas are stated in Conjecture 4.5 of arXiv:2407.06338 and are quantified over every n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, arXiv searches and repository checks recorded
above.
