---
slug: crim-rectair-square-conjecture-two-refutation
bibkey: basic2026crim
doi: 10.48550/arXiv.2606.16828
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.result
---

# Refutation of the CRIM square-rectair formula at its boundary

## Problem

Bašić, Gottlieb, and Krnc, *CRIM: A Natural Game on Integer Partitions*,
arXiv:2606.16828v1, printed page 18, Conjecture 2 states a three-branch
Sprague-Grundy formula for every square rectair `R^k_{r,r}` with
`0 <= k < r`.

The formal claim quantifies natural numbers `r` and `k` with `k < r` and
uses the published three branches: value zero when `r` is even or
`k < r - 1`, value one for `r` equal to 3 or 5, and value two otherwise.

## Motivation

The boundary values `r = 1` and `k = 0` give the one-cell partition `[1]`.
Its only resulting position is the empty partition, whose value is zero, so
the least excluded follower value is one. The printed formula instead gives
two. Therefore the universal conjecture is false.

## Gap

The result concerns the literal formula printed in arXiv version 1. It does
not propose a corrected formula or make a claim about later versions.

## Route

The Lean proof specializes the conjecture at `r = 1`, `k = 0`, unfolds the
frozen well-founded Grundy definition, and kernel-checks the moves and mex
computations. It imports the frozen `grundy`, `rectair`, `moves`, and `mex`
definitions from `CrimGrundyRefutation`.

## Falsifier

A proof of the printed universal claim would contradict
`D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.result`, which
proves its negation at the displayed boundary values.

## Evidence

- Lean module: `D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.lean`.
- Main theorem: `result : Not claim`.
- Literature source: DOI `10.48550/arXiv.2606.16828`, version 1.

## Triage

`theorem`. The result refutes the printed Conjecture 2 only and asserts no
priority or corrected conjecture.

## ASSUMED-UNVERIFIED

The literature search is bounded to the cited arXiv version and repository
records; no exhaustive search or priority claim is made. Google Scholar and
non-arXiv or journal settlements were not exhaustively checked.
