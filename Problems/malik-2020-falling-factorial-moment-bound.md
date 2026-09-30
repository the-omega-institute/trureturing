---
slug: malik-2020-falling-factorial-moment-bound
bibkey: malik2020entropy
doi: null
url: https://arxiv.org/abs/2004.07168v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/FallingFactorialMomentBound.result
---

# A bound on n² times a falling factorial

## Problem

T. A. Malik and R. Lopez-Mobilia (arXiv:2004.07168, cond-mat.stat-mech) define
an entropy through the number of samples needed to see a repeated microstate.
After eq. (003.21) they state:

> Conjecture. (n²/k') (1/k')^n k'!/(k'−n)! ≤ 1 for integer n ∈ [0, k'].

with "We have not found a proof for this conjecture. However, we have analyzed
it numerically and it seems to hold." Issue #11361 fixes the reading: for every
integer `k ≥ 1` and every integer `0 ≤ n ≤ k`, equivalently
`n² · k(k − 1)⋯(k − n + 1) ≤ k^{n+1}`.

## Motivation

The bound gives the corollary `h(k') ∈ (1/k', k')` for the sum `h` of
eq. (003.21), which the paper uses to estimate its entropy for black holes. The
frozen declaration `D5/S3/StatisticalMechanics/FallingFactorialMomentBound.result`
proves the conjecture for all `k ≥ 1` and `0 ≤ n ≤ k`; the corollary and its use
are not formalized.

## Gap

Issue #11361 preregisters the reading, the route and the literature check. The
paper has one arXiv version and no journal reference; INSPIRE lists no citing
record. The product estimate `∏(1 − i/k) ≤ e^{−n(n−1)/2k}` is the standard
birthday-problem bound; no source found states this inequality.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. For `n ≤ 3` the inequality is a polynomial one: `4(k − 1) ≤ k²` for `n = 2`,
   and `k⁴ − 9k(k − 1)(k − 2) = k((k − 3)³ + 9) ≥ 0` for `n = 3`.
2. For `n ≥ 4`, `k(k − 1)⋯(k − n + 1) = k^n ∏_{i<n}(1 − i/k) ≤ k^n e^{−u}` with
   `u = n(n − 1)/(2k)`, by `1 − x ≤ e^{−x}`.
3. `u e^{−u} ≤ e^{−1} < 3/8` gives `(n − 1) n² e^{−u} = 2nk · u e^{−u} ≤ (3/4) nk ≤ (n − 1) k`
   for `n ≥ 4`, so `n² e^{−u} ≤ k`.

## Falsifier

The answer would change if `n²` were replaced by `(n + 1)²` (then `(n, k) = (1, 1)`
fails) or if the normalisation `1/k` were weakened to `1/(k − 1)` (then
`(n, k) = (2, 2)` fails).

## Evidence

Exact integer arithmetic for `k ≤ 400` (issue #11361): no violation; equality
exactly at `(n, k) = (1, 1)` and `(2, 2)`.

The canonical source is
`D5/S3/StatisticalMechanics/FallingFactorialMomentBound.lean`. Its public
declarations are `claim` and `result`. The frozen module state has statement
identity
`sha256:de1cdcb3b1d5b50c78d2bde4372d647415453086254e5dd5e136bb0a8ef55f82`.
The result declaration has statement identity
`sha256:dd1798e2998f5227f1b0b00414c60259bb5a01d7333a8574e2bb4c4cb5d2ca5e`.
The Freeze event is
`sha256:36d4310f9d36478f31bab174ceb44e7a5f6f30201d75478fe11be4e24b70e993`
and has no project-level frozen prerequisites. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #11361 before any
Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the case split, the product bound and the one-variable
bound are proved in the module. Its escape witness is form (1), and its
admission basis is `open-problem-resolution`. Utility `none`: the inequality is
proved for all `k` and `n`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent answer. The Lean kernel does not
authenticate the external source or its version history.
