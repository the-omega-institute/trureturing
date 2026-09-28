---
slug: mathar-2012-a026023-recurrence
bibkey: mathar2012a026023
doi: null
url: https://oeis.org/A026023
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.result
---

# Mathar's recurrence for the surviving walks A026023

## Problem

OEIS A026023 counts the sequences `s(0), …, s(n)` of nonnegative integers with
`|s(i) − s(i − 1)| = 1` and `s(0) = 3`; by a comment of R. M. Ziff, `a(n)/2^n`
is the probability that a random walker started at `x = 4` has not been
adsorbed at `x = 0` by time `n`. Its formula field records:

> Conjecture: (n+4)*(n-1)*a(n) +(n-1)*(n+1)*a(n-1)
> -2*(n+1)*(2*n+1)*a(n-2) -4*(n-1)*(n+1)*a(n-3)=0. - _R. J. Mathar_, Sep 29
> 2012

Issue #10761 fixes the reading: `a` is the entry's name read literally, the
recurrence is asserted for every `n ≥ 3` and read in `ℤ`.

## Motivation

The entry still marks the recurrence as a conjecture (revision 47,
2025-10-13). `D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.result`
proves it for every `n ≥ 3` from the literal walk definition.

## Gap

Issue #10761 preregisters the proof route and the literature check; the
entry's history records no proof, and the papers proving batches of Mathar's
conjectures do not treat A026023. `not-found-in-searched-scope`.

## Route

1. Splitting on the first step, `W(n + 1, x) = W(n, x + 1) + [x ≥ 1] W(n, x − 1)`
   for the number `W(n, x)` of walks of length `n` from `x`.
2. The reflection count `Σ_{n < 2d + x + 2, 2d ≤ n + x} C(n, d)` satisfies the
   same recursion by Pascal's rule, so it equals `W(n, x)` (Theorem 2.1 of
   Jianu and Dăuş 2025, entering as a local step of the proof).
3. At `x = 3`: `a(2m) = C(2m + 2, m)` and `a(2m + 1) = 2 C(2m + 2, m)`.
4. With `c(m) = C(2m + 2, m)`,
   `(m + 1)(m + 3) c(m + 1) = 2(m + 2)(2m + 3) c(m)`; the recurrence
   expression is `12` times this relation for odd `n`, and `j + 2` times it
   is a combination of the relations at `j + 1` and `j` for even `n = 2j + 4`.

## Falsifier

The proof would fail if the walk count differed from the reflection count, or
if the combinations of step 4 did not reproduce the recurrence expression for
some `n ≥ 3`.

## Evidence

Exact integer computation: the literal definition by brute force matches the
recursion for `n ≤ 14`, the walk count reproduces the 34 data terms, the
recurrence holds for `n = 3, …, 400`, and replacing the leading factor `n + 4`
by `n + 5` fails for every such `n` (issue #10761).

The canonical source is
`D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence.lean`. Its
public declarations are `walks`, `a`, `claim`, and `result`. The frozen module
state has statement identity
`sha256:623ab7879bf31a0a1aa4630d573480d1ca1de9ff570ac9ceae6e95312d1284cc`.
The result declaration has statement identity
`sha256:6edcfcebe2f131c3bfce97e661f25c580c694d3a21e0e4f4650fad7e76612054`.
The Freeze event is
`sha256:7cf33fc8bf2901d835ef1093573a5837afaa23e07771a8369bc7b0c0a4cb1b50`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (OEIS formula field), preregistered in issue
#10761 before the probe. `theorem`; resolution `proved`. The public theorem
has `proof_shape: content`: the first-step bijection and the identification
of the walk count with the reflection count (Jianu and Dăuş 2025, Theorem 2.1)
are new propositions on its live path. Admission basis
`open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
