---
slug: bhagat-kulkarni-larsson-murali-conjecture-4-refutation
bibkey: bhagatkulkarnilarssonmurali2026tiebreaking
doi: null
url: https://arxiv.org/abs/2510.24280v2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.result
---

# Refutation of Bhagat, Kulkarni, Larsson and Murali Conjecture 4

## Problem

Conjecture 4 of arXiv:2510.24280v2 states:

> Consider any subtraction set S, and suppose both players act friendly in case of indifference. Then each player's PSPE utility is never worse than if both players have antagonistic tie-breaking rules.

The paper orders outcome pairs coordinatewise. In the formal reading, a finite nonempty duplicate-free list of positive natural numbers represents S, and both coordinates of the AvA outcome are required to be at most the corresponding FvF coordinates for every natural heap.

## Motivation

This is a named external conjecture in a published arXiv paper. Issue #8521 preregistered its verbatim statement, the full quantifiers, the candidate counterexample, and the literature check before the kernel probe. The frozen result settles the literal conjecture by a typed refutation.

## Gap

The paper proves the two-element case and reports no method for arbitrary subtraction sets. Its numerical discussion reports no positive FvF-to-AvA discrepancy for the tested random sets, but does not prove the universal claim. The checked source and repository surfaces contained no prior settlement of this Conjecture 4 statement. These checks do not establish exhaustive literature coverage or publication priority.

## Route

Use the repository's finite subtraction-game outcome recurrence with the four-step list `[4, 22, 35, 38]`. Kernel reduction gives
`outcome S FvF 161 = (84, 77)` and
`outcome S AvA 161 = (83, 78)`. The second coordinate would require `78 <= 77`, which is false.

## Falsifier

A proof of the coordinatewise FvF-to-AvA inequality for every finite nonempty positive subtraction set and every heap would falsify this refutation. Rechecking the outcome recurrence or either kernel-computed pair would also require rechecking the result.

## Evidence

- Lean module: `D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.lean`.
- Frozen declarations: `claim`, `witnessSubtractions`, and `result`; the resolution theorem is `result : Not claim`.
- The source mirror records the counterexample values and the coordinatewise failure; the `result` proof checks the two outcome pairs with `decide +kernel` and derives the contradiction with `omega`.
- The only repository prerequisite is the frozen `D5/S0/Certificates/SelfInterestConventionDeviationGain` module, which supplies the outcome definitions and recurrence.

## Triage

`theorem`; resolution `refuted` for the literal Conjecture 4 statement. This result asserts no minimality, classification, corrected inequality, or claim about other subtraction sets.

## ASSUMED-UNVERIFIED

The correspondence between the paper's PSPE terminology and the repository's outcome recurrence is a source-faithfulness judgment, not a kernel theorem. The literature search was bounded to the cited paper, the repository, and the recorded issue checks; exhaustive coverage and publication priority remain unverified. No claim is made about whether another counterexample is smaller.
