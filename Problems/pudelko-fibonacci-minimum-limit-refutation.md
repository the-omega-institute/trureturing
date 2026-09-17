---
slug: pudelko-fibonacci-minimum-limit-refutation
bibkey: pudelko2025modular
doi: null
url: https://arxiv.org/abs/2510.24882v5
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.result
---

# Pudelko Conjecture 8: the Fibonacci minimum probability at zero

## Problem

Pudelko, *Modular Periodicity of Random Initialized Recurrences*,
arXiv:2510.24882v5, section 3, Conjecture 8 states:

> Consider either the Fibonacci recurrence a_n = a_{n-1} + a_{n-2} or its
> parity recurrence a_n = -a_{n-1} + a_{n-2} with random integer
> initialization {a_0, a_1} in Z^2. Although these sequences diverge as
> n tends to plus or minus infinity, they possess well-defined absolute
> minima.

Its displayed formula (13) gives `P(0) = 1/4`. The following remark supplies
the bounded interpretation used here:

> However, for bounded initializations {a_0, a_1} in [-N, N]^2 intersect
> Z^2, the ratio r = a_0/a_1 takes only finitely many rational values,
> imposing a finite resolution on the real line. We therefore expect
> P_N(n) = P(n) + epsilon(N), epsilon(N) tends to 0 as N tends to infinity.

Preregistration issue #8469 fixes the Fibonacci recurrence and the `n = 0`
clause. For initial values `(x,y)`, let the bilateral recurrence have values
`x` and `y` at positions zero and one. Let `min0(x,y)` mean that the absolute
value at zero is at most the absolute value at every integer position, so
ties are allowed. Define `P_N(0)` as the fraction of pairs in `[-N,N]^2`
that satisfy `min0`. The resolved assertion is

```text
forall epsilon > 0, exists N0, forall N >= N0,
  abs(P_N(0) - 1/4) < epsilon.
```

## Motivation

The bounded-square statement is the paper's operational interpretation of
uniform random integer initialization. Allowing every tie makes the counted
set at least as large as it is under any stricter tie rule, so an upper bound
for this set also applies to those rules.

## Gap

The arXiv API returned one exact-title record and version 5 still labels the
statement Conjecture 8. The bounded audit recorded in issue #8469 found no
later proof or refutation. The search was limited to the reported arXiv and
citation surfaces and does not establish publication priority.

## Route

If `x > 0` and zero is a global absolute-value minimizer, the values at
indices `1`, `2`, `-1`, and `-2` force `y >= 3x` or `y <= -2x`. Negation
gives the corresponding two cones for `x < 0`, while `x = 0` contributes one
vertical line.

Counting those regions in the square of radius `6t` gives at most
`30t^2 + 10t + 1` admissible pairs. For every `t >= 3`, division by
`(12t+1)^2` gives `P_(6t)(0) <= 2/9`. Taking `epsilon = 1/72` contradicts
convergence to `1/4` along this unbounded subsequence.

## Falsifier

A proof that the bounded-square probabilities converge to `1/4` would
contradict the kernel-checked estimate on the subsequence `N = 6t`. A change
to the recurrence, the initialization domain, or the meaning of an absolute
minimum would address a different statement.

## Evidence

`D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.lean` defines the
bilateral Fibonacci sequence, `min0`, the bounded probability, and the
convergence claim. Its theorem `result : Not claim` has exactly the standard
axiom closure `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`: the `n = 0` Fibonacci clause of Conjecture 8 under equation (14)'s
bounded-square interpretation is refuted. No parity-recurrence clause and no
claim about another minimum position is resolved.

## ASSUMED-UNVERIFIED

The literature audit is bounded and does not establish exhaustive coverage
or historical publication priority. The source-to-formalization mapping uses
the most permissive tie convention; the paper does not specify a different
formal tie-breaking rule for equation (14).
