---
slug: gottlieb-krnc-mursic-pnim-heavy-interval-refutation
bibkey: gottlieb2025pnim
doi: 10.48550/arXiv.2506.04991
url: https://arxiv.org/abs/2506.04991
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/PnimHeavyIntervalRefutation
---

# Refutation of the PNim heavy-interval conjecture

## Problem

Gottlieb, Krnc, and Mursic, *Nim on Integer Partitions and Hyperrectangles*,
arXiv:2506.04991v1, printed page 14, Conjecture 2 states that whenever the
rectangle `[a+1]^(b+1)` is heavy, every partition in the Young interval from
`[a+1,a,...,a-b+1]` to that rectangle is heavy.

The formal claim is the fully quantified natural-number version with
`b <= a`, the PNim row and column moves, the recursive Grundy value, and the
definition of heaviness from Proposition 2.

## Motivation

The kernel-checked counterexample takes `a = 8`, `b = 7`. The upper rectangle
`[9,9,9,9,9,9,9,9]` is heavy, while the intervening partition
`[9,9,8,8,8,5,5,5]` has Grundy value `3` and longest-play length `16`.
Therefore the printed universal conjecture is false.

## Gap

The dossier records the printed conjecture and its explicit counterexample;
it makes no claim about later journal versions or corrected formulations.

## Route

The Lean proof checks finite certificates for the two relevant Grundy values,
then specializes the universal claim at `a = 8`, `b = 7` and the intervening
partition.

## Falsifier

A proof of the printed universal claim would contradict
`D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.result`, which proves
its negation at the displayed parameters.

## Evidence

- Lean module: `D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.lean`.
- Main theorem: `result : ¬ claim`.
- Literature source: DOI `10.48550/arXiv.2506.04991`, version 1.

## Triage

`theorem`. The result refutes the printed Conjecture 2 only and asserts no
priority or corrected conjecture.

## ASSUMED-UNVERIFIED

The literature search is bounded to the cited arXiv version and repository
records; no exhaustive search or priority claim is made.
