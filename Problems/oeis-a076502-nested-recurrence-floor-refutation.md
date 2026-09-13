---
slug: oeis-a076502-nested-recurrence-floor-refutation
bibkey: cloitre2002a076502
doi: null
url: https://oeis.org/A076502
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation
---

# Refutation of the A076502 nested-recurrence floor-offset conjecture

## Problem

OEIS A076502 %N (verbatim):

> a(1)=1, a(n)=n-a(n-a(n-a(n-1)))

%C (verbatim; Benoit Cloitre, Nov 08 2002):

> Conjecture : a(n) - c*n is bounded and a(n)=floor(c*n) + 0 + 1 or +2 - _Benoit Cloitre_, Nov 08 2002

%F (verbatim; Benoit Cloitre, Nov 08 2002):

> a(n) is asymptotic to c*n with c=0.5698..is the positive root of x^3-x^2+2*x-1 - _Benoit Cloitre_, Nov 08 2002

The literal objects are the nested recurrence, `c` as the unique positive root
of `x^3-x^2+2*x-1`, and the conjunction that `a(n)-c*n` is bounded and
`a(n) = floor(c*n) + 0, 1 or 2` for every positive `n`. The formal theorem
refutes only the second conjunct, which refutes the conjunction.

## Motivation

Cloitre's 2002 comment gives a precise universal floor-offset conjecture for a
concrete nested recurrence and algebraic constant. A certified counterexample
settles that conjunction without changing the recurrence or making a claim
about its bounded-error or asymptotic clauses.

## Gap

Preregistration issue #7479 and its probe report record searches dated
September 13, 2026. OEIS history revisions #1 through #6 contain only
formatting or metadata changes. Exact searches returned 0 results on the
arXiv web interface, 0 on OpenAlex, 0 on MathOverflow, and 0 on GitHub. The
arXiv API returned HTTP 429. No resolution was found in those bounded surfaces.
This does not assert exhaustive literature coverage or publication priority.

## Route

The index invariant `1 <= a(k) <= k` makes the nested recursion total and shows
that both clamps in its definition are identities, yielding the literal source
recurrence. A kernel-checked balanced prefix certificate gives
`a(1167) = 664`.

For `P(x) = x^3-x^2+2x-1`, strict increase follows from
`2*(P(y)-P(x))/(y-x) = x^2+y^2+(x+y-1)^2+3` when `x<y`; the right side is
positive. The intermediate value theorem on `[0,1]` therefore gives a unique
positive root `c`. Exact rational evaluation gives
`P(665/1167) < 0 < P(666/1167)`, hence `floor(1167c) = 665`. Thus
`a(1167)-floor(1167c) = 664-665 = -1`, which is not in `{0,1,2}`.

## Falsifier

The refutation would fail if the index bounds did not justify the literal
unclamped recurrence, if the checked prefix value at 1167 were not 664, if the
cubic were not strictly increasing with its unique positive root between the
two stated rationals, or if `-1` belonged to `{0,1,2}`. The Lean theorem checks
all four links.

## Evidence

- Lean module:
  `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- The kernel check for `result` took 4.05 seconds.
- The orchestrator evaluated the exact recurrence through 3000 and used
  rational bisection; the violations were exactly
  `1167, 1253, 2248, 2334, 2599, 2685`.
- The probe independently reproduced the same six violations.

## Triage

`theorem`. The certified instance at `n = 1167` refutes the universal
floor-offset conjunct and therefore the printed conjunction.

## ASSUMED-UNVERIFIED

The arXiv API returned HTTP 429, so no API-complete arXiv search is claimed.
The literature search was bounded to the dated surfaces above. Nothing here
claims that `a(n)-c*n` is or is not bounded, or proves the asserted asymptotic.
