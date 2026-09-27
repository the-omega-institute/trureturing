---
slug: erdos-1979-exactly-one-divisor-unimodality
bibkey: tenenbaum2013unconventional
doi: 10.1007/978-3-642-39286-3_23
triage: theorem
motivation_gids:
  - D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation
---

# Refutation of the one-divisor interval-density unimodality suggestion

## Problem

Erdős, *Some unconventional problems in number theory*, Astérisque 61 (1979),
printed page 78:

> Perhaps ε₁(n,m) is unimodular for m > n+1, but I know nothing about this.

Here `ε₁(n,m)` is the natural density of integers `N` having precisely one
divisor `d` with `n < d < m`. Tenenbaum, *Some of Erdős' Unconventional Problems
in Number Theory, Thirty-four Years Later* (2013), printed page 18, states:

> To my knowledge, the question of unimodality of ε₁(y,z) as a function of z is still open.

Tenenbaum writes the upper endpoint as `d <= z`; the formal refutation follows
the strict upper endpoint in Erdős's original sentence.

## Motivation

The 1979 paper poses an elementary distribution-of-divisors question, and the
2013 chapter records it as still open. Exact densities for one fixed value of
`n` can refute the unqualified assertion without an asymptotic estimate.

## Gap

The question is erdosproblems.com problem 692 (`https://www.erdosproblems.com/692`),
recorded there as disproved: Stijn Cambie, *Resolution of Erdős' problems about
unimodularity*, arXiv:2501.10333 (2025), shows that `δ₁(n,m)` is not unimodal
for `n = 2` and `n = 3` and that for fixed `n` the sequence has superpolynomially
many local maxima; a Lean formalization of the negative answer by Monticone is
linked from that page, and `google-deepmind/formal-conjectures`
(`FormalConjectures/ErdosProblems/692.lean`) marks the unimodality part solved
with the same reference. The refutation below therefore certifies, in this
repository's kernel, a statement already refuted in 2025; it is not a first
resolution. Tenenbaum's 2013 remark predates Cambie's paper. R. R. Hall's 1992
paper *On some conjectures of Erdős in Astérisque, I*, DOI
`10.1016/0022-314X(92)90096-8`, remains unread here (publisher HTTP 403).

## Route

For fixed `n,m`, membership in the set of integers having exactly one divisor
in `(n,m)` is periodic with period the least common multiple of the integers in
that interval. Its density is obtained by binding the frozen theorem
`D5/S3/ObserverMemory/Prediction/EventualCycleAverage.eventual_cycle_average`
to the finite orbit on `Fin P` with the event's zero-one indicator as the
observable. The resulting cycle average is the number of members in `[0,P)`
divided by `P`.

For `n=2`, the periods and favorable residue counts at `m=6,7,8` are
`(60,26)`, `(60,22)`, and `(420,156)`. Hence the respective densities are
`13/30`, `11/30`, and `13/35`, a strict valley. Weak unimodality means that
there is a mode at or after the beginning of the tail, with the function
nondecreasing up to the mode and nonincreasing from the mode onward. The
theorem `not_unimodal_of_valley` proves that any strict valley on the tail
rules out this shape: a mode after the valley bottom contradicts the preceding
fall, while a mode at or before it contradicts the later rise.

## Falsifier

A correction to any of the three period counts, a failure of the periodic-set
density theorem, or evidence that the printed assertion had an omitted lower
bound on `n` would invalidate this refutation of the stated claim.

## Evidence

- Module: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.lean`.
- Frozen density input:
  `D5/S3/ObserverMemory/Prediction/EventualCycleAverage.eventual_cycle_average`.
- Escape content: `not_unimodal_of_valley`.
- Formal claim and refutation: `claim` and `result`.
- Axiom closure for both `not_unimodal_of_valley` and `result`: std3
  (`propext`, `Classical.choice`, `Quot.sound`).
- Formal exact values: `ε₁(2,6)=13/30`, `ε₁(2,7)=11/30`, and
  `ε₁(2,8)=13/35`, from full periods with counts `26/60`, `22/60`, and
  `156/420`.
- The orchestrator independently enumerated the six full-period values for
  `m=4,...,9`: `1/3`, `5/12`, `13/30`, `11/30`, `13/35`, `11/35`, with
  periods `3`, `12`, `60`, `60`, `420`, `840` and favorable counts `1`, `5`,
  `26`, `22`, `156`, `264`.

## Triage

`theorem`. The universal printed suggestion is refuted by the `n=2` strict
valley, and the resolution is attached only to `result`.

## ASSUMED-UNVERIFIED

Hall's 1992 paper was not read. The literature search is bounded to the checked
surfaces listed above and does not establish first-publication priority. Only
the unqualified printed statement is refuted; a repaired variant restricted to
sufficiently large `n` is not addressed. The separate question of where the
density attains its maximum is not addressed. GitHub code search required an
authenticated session and was not checked.
