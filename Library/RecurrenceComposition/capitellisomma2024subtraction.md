---
bibkey: capitellisomma2024subtraction
authors: Nicolás Capitelli, Francisco Somma
year: 2024
title: On sequences arising from randomizing subtraction games
doi: 10.48550/arXiv.2405.19593
url: https://arxiv.org/abs/2405.19593v1
claim: "Section 3 conjectures nonconvergence for all-odd finite subtraction sets with gcd one; Section 1 defines the uniformly randomized legal-move winning probability."
strata_touched:
  - D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence
license: citation-only
triage: anchor
---

# Capitelli and Somma: randomized subtraction games

## Verified locator

DOI: 10.48550/arXiv.2405.19593

Source: https://arxiv.org/abs/2405.19593v1

## Source definitions

Section 1, p. 2:

> At a given position (number of chips in the pile) 0 ≤ m ≤ n, an element k′ ∈ {k ∈ S | k ≤ m} is randomly selected with equal probability, and the next player to move removes k′ chips from the pile.

> The first player who is confronted with a position m for which {k ∈ S | k ≤ m} = ∅, loses.

Equation (2), p. 2, recursively removes the largest subtraction below its threshold and otherwise averages all follower probabilities. `legalMoves S n` filters a finite set of natural numbers by `0 < s ∧ s ≤ n`; `winProb S n` is zero without a legal move and otherwise one minus the uniform average over legal followers. Natural subtraction is truncated and division of probabilities is real division.

## All-odd conjecture

Section 3, p. 7, assumes `S = {k₁, …, kₜ} ⊂ ℕ`, with increasing entries and gcd one, and states:

> However, we do not show that an all-odd subtraction set necesarily do not converge (although we conjeture it) nor we provide the exact limits of the even and odd subsequences for the (conjectured) non-convergent case.

The formal proposition quantifies over finite nonempty sets of odd natural numbers, retains the gcd-one hypothesis, and asserts the absence of any real limit. Odd natural numbers are positive. Its proof uses a nonnegative adjacent-sum transform and a positive conserved finite window, and does not need the gcd-one hypothesis. Subsequence limits and Conjecture 3.3 on simplicity of roots are outside this result.

## Literature boundary

The source is arXiv v1. The literature screen in issue https://github.com/the-omega-institute/trureturing/issues/19195 reports no prior settlement in the checked author lists, citation index and subtraction-game references. Literature completeness is ASSUMED-UNVERIFIED; the missing Semantic Scholar citation list returned HTTP 429. No worldwide priority claim follows from this bounded search.
