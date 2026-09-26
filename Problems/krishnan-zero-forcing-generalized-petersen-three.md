---
slug: krishnan-zero-forcing-generalized-petersen-three
bibkey: krishnan2026correction
doi: 10.48550/arXiv.2607.19412
url: https://arxiv.org/abs/2607.19412v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result
---

# The Zero Forcing Number of P(n,3) Is Eight for Every n At Least Thirteen

## Problem

Arnav Krishnan, *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*, arXiv:2607.19412v1, Conjecture 5:

> Z(P(n,3)) = 8 for every n ≥ 13.

The paper proves the upper bound for `n ≥ 9` (Proposition 4) and the lower bound for `13 ≤ n ≤ 20` by exhaustive search, and states that a
lower-bound proof valid for all `n` is missing.

## Motivation

The frozen theorem `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result` proves the conjecture for every `n ≥ 13`. The lower-bound
argument transfers a statement about forcing sets into a vertex-isoperimetric inequality for `P(n,3)`, and the isoperimetric inequality is
reduced from arbitrary `n` to finitely many column patterns by deleting empty columns.

## Gap

Issue 9685 records the screen made before the work: the arXiv record has only v1, the searched formal-conjecture catalogues have no entry,
and nothing under `Problems/`, `D5/` or `Library/`, and no entry of the three screening records, concerns this paper.

## Route

1. Upper bound: the eight consecutive outer vertices `u_0, …, u_7` force `P(n,3)` for every `n ≥ 9`.
2. First forcers: for any finite graph, if a zero forcing set `S` performs at least `p` forces, the set `X` of its first `p` forcing vertices
   satisfies `|N(X)| ≤ |S|`.
3. Isoperimetry: for every `n ≥ 14`, every 10-vertex set `X` of `P(n,3)` has `|N(X)| ≥ 8`. Seven consecutive empty columns can be shortened by
   one column without changing `|X|` or `|N(X)|`, so it suffices to treat bounded gap patterns; these are exhausted by kernel-checked interval
   covers of the remaining layer codes.
4. Steps 2 and 3 exclude 7-vertex forcing sets for `n ≥ 14`.
5. `n = 13`: explicit forts, checked in the kernel, meet every 7-vertex candidate up to rotation.

## Falsifier

The statement would fail if some `P(n,3)` with `n ≥ 13` had a 7-vertex zero forcing set, equivalently if a 10-vertex set of `P(n,3)`,
`n ≥ 14`, had external boundary at most 7 and could be the first-forcer set of such a forcing process, or if a 7-vertex set of `P(13,3)` met
no fort.

## Evidence

SAT checks with CaDiCaL: "`|X| = p` and `|N(X)| ≤ 7`" is unsatisfiable for `p = 10` and every `14 ≤ n ≤ 40` and satisfiable at `n = 13`;
for `p ≤ 9` it is satisfiable for every tested `n`, so ten first forcers are the least number that works.

## Triage

`theorem`; Tier 1 open problem stated in a 2026 paper, preregistered in issue 9685 before the work. The finite parts (the `n = 13` fort
certificates and the interval covers of bounded gap patterns) are checker instances consumed by the general proof, recorded in the module
headers.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources named above; no worldwide priority claim is made.
