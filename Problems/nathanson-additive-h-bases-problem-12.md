---
slug: nathanson-additive-h-bases-problem-12
bibkey: nathanson2026hbases
doi: null
url: https://arxiv.org/abs/2605.26425v3
triage: theorem
motivation_gids:
  - D5/S3/Arith/NathansonAdditiveHBasisRefutation.result
---

# Refutation of Nathanson's additive h-basis strict inequality

## Problem

Problem 12(2) of arXiv:2605.26425v3 asks whether, for integers `h >= 2` and
`k >= 2`, every `k`-element integer set `A` with a negative element satisfies
`ell_h(A) < n-flat_h(k)` whenever `ell_h(A)` is defined.

## Motivation

The preregistered issue #8540 records the literal quantifiers, the source
statement, and the candidate counterexample before formalization. The source
prints `A = {-1, 1, 2}` as a reflection example, while Problem 12(2) asks
whether the strict inequality holds universally.

## Gap

The checked source and repository searches found no earlier formal settlement
of this exact Problem 12(2) statement. This dossier does not claim exhaustive
literature coverage or publication priority.

## Route

At `h = 2`, `k = 3`, and `A = {-1, 1, 2}`, the double sumset is
`{-2, 0, 1, 2, 3, 4}`, so the covered initial segment reaches 4. The
nonnegative three-set maximum is also 4: `{0, 1, 2}` reaches 4, while a
three-element set whose double sumset covers 0 through 5 must contain 0 and 1;
representing 3 then forces the third element to be 2 or 3, and neither case
represents 5.

## Falsifier

A proof of the literal universal strict inequality in Problem 12(2) would
contradict the frozen theorem `D5/S3/Arith/NathansonAdditiveHBasisRefutation.result`.

## Evidence

- Frozen result: `D5/S3/Arith/NathansonAdditiveHBasisRefutation.result`.
- The result has type `Not claim` and is kernel-checked in the pinned Lean
  toolchain.
- The witness bound `nonnegativeMaximum 2 3 <= 4` is proved by the explicit
  case analysis in the result proof, not by a finite search shortcut.

## Triage

`theorem`; resolution `refuted` for the literal strict statement only. No claim
is made about Problem 12(1), other parameter values, minimality, or a corrected
inequality.

## ASSUMED-UNVERIFIED

The literature search is bounded to the cited arXiv source, repository surfaces,
and the preregistered checks. Exhaustive coverage and publication priority remain
unverified.
