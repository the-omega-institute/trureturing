---
slug: zelinsky-zhang-conjecture-22-refutation
bibkey: zelinskyzhang2025klprimitive
doi: 10.48550/arXiv.2501.04209
url: https://arxiv.org/abs/2501.04209v2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation
---

# Refutation of Zelinsky and Zhang's Conjecture 22

## Problem

Zelinsky and Zhang, *Kullback-Leibler divergence and primitive non-deficient
numbers*, arXiv:2501.04209v2, page 14, Conjecture 22 (verbatim):

> Assume that n is a positive integer and assume that
> n is not in {1, 12, 24, 30, 36, 48, 60, 72, 120, 180, 240, 360}.
> Let p be the smallest prime factor of n. Then v(n) >= 1/p^2.

For a positive integer n, the paper defines
`v(n) = sum_{d | n, d > 1} (1/d) log((tau(n) - 1)/d)`.
The literal claim formalized here quantifies over every positive natural n,
uses exactly the twelve published exclusions, and takes p to be
`Nat.minFac n`. No additional restriction on n is imposed.

## Motivation

The published universal lower bound has a small exact counterexample. A
kernel-checked refutation separates the literal statement from any corrected
variant without adding a hypothesis that would weaken the published claim.

## Gap

Preregistration issue #8415 records the statement and proposed counterexample
before the Lean probe. On September 17, 2026, the arXiv abstract record listed
only versions v1 (January 8, 2025) and v2 (February 6, 2025), with zero matches
for `withdrawn`, `erratum`, or `Errata`. A fresh `origin/dev` duplicate search
found no occurrence of arXiv:2501.04209 and no existing module with this
divisor-weighted definition or its refutation. These are bounded surfaces; no
priority claim is made.

## Route

At n = 6, the positivity and exclusion hypotheses hold and
`Nat.minFac 6 = 2`. Kernel reduction gives
`Nat.divisors 6 = {1, 2, 3, 6}`, so

`v(6) = (1/2) log(3/2) + (1/6) log(1/2)`.

`Real.log_lt_sub_one_of_pos` gives `log(3/2) < 1/2`, while `Real.log_neg`
gives `log(1/2) < 0`. Therefore `v(6) < 1/4`, contradicting the conjectured
lower bound `1/(Nat.minFac 6)^2 = 1/4`.

## Falsifier

A proof of the literal universal claim would specialize at n = 6 to
`1/4 <= v(6)`. The exact logarithmic inequalities in the kernel theorem give
the strict opposite inequality, so such a proof contradicts
`D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.result`.

## Evidence

- Lean module:
  `D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.lean`.
- Main theorem: `result : not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The divisor identity is checked by `decide +kernel`; the proof uses no
  numerical approximation and no `native_decide`.
- The source-bound Lean report records the claim and result as same-module,
  included, closed declarations and records the result as a closed negation
  of the claim.
- The only retained explicit import is `Mathlib.Tactic`; deleting it makes the
  build fail, while the two deleted direct imports were redundant.

## Triage

`theorem`. The explicit certified instance refutes the literal universal
statement. The proof shape is `bind-only`, the admission basis is
`open-problem-resolution`, and the utility basis is the typed `refutes` edge
from `result` to `claim`. No corrected lower bound is asserted.

## ASSUMED-UNVERIFIED

The literature check is bounded to the current arXiv record and the stated
repository duplicate-search surfaces. Exhaustive publication coverage and
priority were not verified and are not claimed.
