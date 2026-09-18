---
slug: pudelko-fibonacci-minimum-limit-refutation
bibkey: pudelko2025modular
doi: null
url: https://arxiv.org/abs/2510.24882v5
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.result
---

# Refutation of Pudelko Conjecture 8 at position zero

## Problem

Pudelko, *Modular Periodicity of Random Initialized Recurrences*,
arXiv:2510.24882v5, Conjecture 8, proposes that the probability of a
Fibonacci sequence having its absolute minimum at position zero is one
quarter. Equation (14) gives the bounded-initialization interpretation:

> P_N(n) = P(n) + epsilon(N), epsilon(N) -> 0 as N -> infinity.

For integer initial values `(x,y)` in the inclusive square `[-N,N]^2`, the
formal statement counts position zero whenever its absolute value is no
greater than the absolute value at every integer index. Ties are therefore
included. The resolved clause is the quantified convergence assertion

```text
forall epsilon : Rat, 0 < epsilon -> exists N0 : Nat,
  forall N : Nat, N0 <= N -> abs (P_N(0) - 1/4) < epsilon.
```

## Motivation

Issue #8469 preregistered the verbatim conjecture, its bounded interpretation,
the full quantifiers, and the proposed unbounded-family refutation before the
Lean probe. The frozen theorem settles the Fibonacci, `n = 0` clause without
asserting a replacement limiting distribution.

## Gap

The checked v5 source still presents Conjecture 8 and equation (14) as an
expectation. The bounded literature audit through September 17, 2026 found no
later independent proof or refutation of this clause. The repository and
pinned Mathlib searches found no prior declaration of this bounded minimum
probability or its limit refutation. These are bounded search surfaces and do
not establish exhaustive publication coverage or priority.

## Route

For the bilateral Fibonacci sequence with `a_0=x` and `a_1=y`, the values at
indices `1`, `2`, `-1`, and `-2` are `y`, `x+y`, `y-x`, and `2x-y`. If
`x>0` and position zero is a global absolute-value minimum, comparison with
those four values gives the cone alternative `3x <= y` or `y <= -2x`.
Negating both initial values handles `x<0`, while `x=0` contributes one
vertical segment.

Counting the two cones and their negatives in the square of radius `6t`
gives at most `30t^2+10t+1` admissible pairs. For every `t>=3`, the resulting
probability is at most `2/9`. Taking `epsilon=1/72` and choosing a multiple
`N=6t` beyond any proposed threshold contradicts convergence to `1/4`.

## Falsifier

A proof that the displayed bounded-square probability converges to one
quarter under the inclusive-tie convention would contradict the frozen
theorem `result : Not claim`. A different tie-breaking convention or a
different initialization measure is not the formal claim settled here.

## Evidence

- Lean module:
  `D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.lean`.
- Resolution theorem: `result : Not claim`, with exactly the standard axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- The proof uses an unbounded family of exact symbolic counts and no
  `native_decide`.
- Removing `Mathlib.Algebra.BigOperators.Intervals` makes
  `Finset.sum_range_id_mul_two` unavailable; the retained import is used.

## Triage

`theorem`; resolution `refuted` for Conjecture 8's Fibonacci `n = 0` clause
under equation (14). The proof shape is `bind-only`, the admission basis is
`open-problem-resolution`, and `utility: none` is appropriate because the
result is an unbounded-family estimate rather than a finite certified
instance. No claim is made about the remaining positions, the parity
recurrence, or the correct limiting distribution.

## ASSUMED-UNVERIFIED

The literature audit was bounded. Exhaustive publication coverage and
historical priority were not verified and are not claimed.
