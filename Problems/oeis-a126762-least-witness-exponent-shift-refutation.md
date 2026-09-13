---
slug: oeis-a126762-least-witness-exponent-shift-refutation
bibkey: ordowski2018a126762
doi: null
url: https://oeis.org/A126762
triage: theorem
motivation_gids:
  - D5/S0/Certificates/OrdowskiLeastWitnessRefutation
---

# Refutation of the A126762 least-witness exponent-shift conjecture

## Problem

OEIS A126762, NAME (verbatim):

> a(n) is the least k > n such that the remainder when n^k is divided by k is n.

COMMENT (verbatim; Thomas Ordowski, Aug 03 2018):

> a(n) is the smallest number k > n such that n^k == n (mod k). Conjecture: a(n) is the smallest number k > n such that n^(k-1) == 1 (mod k). Thus a(n) is coprime to n. - _Thomas Ordowski_, Aug 03 2018

The published b-file line `363 366` already contradicts the coprimality
consequence, since `gcd(363, 366) = 3`.

## Motivation

This first-tier OEIS conjecture was printed in 2018 and remains labelled as a
conjecture in the current entry. A certified counterexample resolves the
universal least-witness transfer claim without changing the definition of
A126762.

## Gap

Preregistration issue #7407 records searches dated September 13, 2026 across
all 20 OEIS revisions, the OEIS reverse-reference surface, Crossref, OpenAlex,
the MathOverflow API, and GitHub repositories, commits, issues, and pull
requests. The recorded hit counts were 0 for the exact Crossref identifier,
0 for OpenAlex, 0 for MathOverflow, 0 for GitHub repositories and commits, and
2 for GitHub issues and pull requests, consisting of the repository tracking
issue and an unrelated dependency update. A proof or refutation was not found
in the checked surfaces. The arXiv API and HTML surface returned HTTP 429 and
were not verified. This is a bounded search report, not a claim of exhaustive
coverage or first-publication priority.

## Route

Take `n = 363`. The least `k > 363` satisfying
`363^k ≡ 363 (mod k)` is `366`: the residues of `363^k` modulo `k`
are respectively `1`, `333`, and `363` at `k = 364, 365, 366`.
Proof-local modular-period certificates establish all three values without
evaluating the full powers.

For the proposed condition, `363^365 ≡ 123 (mod 366)`, and
`123 ≠ 1`. Thus `366` is not a witness for the exponent-shift condition,
so `IsLeast` cannot transfer from the first witness set to the second. The
second least witness `367` is not needed for the refutation.

## Falsifier

The refutation would fail if `366` were not the least witness of the first
condition at `n = 363`, or if `363^365` had remainder `1` modulo `366`.
It would also fail if the printed conjecture did not assert that the same
least witness transfers between these two conditions. The Lean theorem checks
the first two alternatives directly, and its `claim` definition records the
third.

## Evidence

- Lean module: `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- Public source definitions: `firstCongruence`, `secondCongruence`, and
  `claim`.
- The first-condition residue table at `k = 364, 365, 366` is
  `1, 333, 363`.
- The second-condition residue table at `k = 364, 365, 366, 367` is
  `363, 16, 123, 1`.
- The orchestrator's independent exact check through `n ≤ 2000` found
  mismatches exactly at `n = 363` and `n = 801`.
- The search seat's exact check through `n ≤ 10^4` found 11 mismatches.

## Triage

`theorem`. The certified instance at `n = 363` refutes the universal
conjecture. It claims nothing about a corrected sequence or the second least
witness `367`.

## ASSUMED-UNVERIFIED

The external search counts beyond the live OEIS entry and b-file are taken
from preregistration issue #7407 and were not recomputed by this implementation
seat. The orchestrator's `n ≤ 2000` mismatch count and the search seat's
`n ≤ 10^4` count were supplied readings and were not repeated here. The
arXiv surface remained unverified because the recorded requests returned HTTP
429. No exhaustive literature or publication-priority claim follows.
