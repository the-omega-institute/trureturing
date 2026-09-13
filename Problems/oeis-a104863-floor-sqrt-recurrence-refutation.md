---
slug: oeis-a104863-floor-sqrt-recurrence-refutation
bibkey: seidov2005a104863
doi: null
url: https://oeis.org/A104863
triage: theorem
motivation_gids:
  - D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation
---

# Refutation of the A104863 floor-square-root recurrence conjecture

## Problem

OEIS A104863, NAME (verbatim):

> a(n) = floor(sqrt(a(n-1)^2 + a(n-2)^2)), a(1)=10, a(2)=30.

FORMULA conjecture line (verbatim; Ralf Stephan, Nov 15 2010):

> For n>=17, a(n) = a(n-2) + a(n-4) + 1 (conjectured). If true then for m>5, a(2*m+1) = 4*F(m) + 25*F(m+1) + 1 and a(2*m+2) = 8*F(m) + 30*F(m+1) + 1 with F(n) = A000045(n). - _Ralf Stephan_, Nov 15 2010

The sequence begins with `a(1) = 10` and `a(2) = 30`, and each later
term is the natural floor square root of the sum of the squares of the two
preceding terms. The literal conjecture is
`∀ n ≥ 17, a(n) = a(n−2) + a(n−4) + 1`.

## Motivation

This OEIS conjecture was printed in 2010 as a universal recurrence for a
sequence introduced in 2005. A certified counterexample resolves the literal
claim. The accompanying numerical checks also distinguish the refutation
from a correction of the printed sign.

## Gap

Preregistration issue #7528 and its probe report record searches dated
September 13, 2026. OEIS history listing pages for revisions #1 through #22
only restate the entry and its conjecture; individual revision pages returned
HTTP 403. Exact searches returned 0 results on arXiv, 0 on Crossref, and 0 on
MathOverflow. OpenAlex, Semantic Scholar, and grep.app were rate-limited, and
GitHub code search was unauthenticated; those surfaces are
`ASSUMED-UNVERIFIED`. No proof or refutation was found in the bounded surfaces
that could be checked. This does not assert exhaustive literature coverage or
publication priority.

## Route

The `Nat.eq_sqrt'` certificates evaluate the defining recurrence through
index 17. In particular, they give `a(13) = 358`, `a(15) = 578`, and
`a(17) = 935`. At the first index covered by the conjecture, its right-hand
side is `578 + 358 + 1 = 937`, which is not 935. Therefore the universal
claim is false at `n = 17`.

## Falsifier

A proof of `a(n) = a(n-2) + a(n-4) + 1` for every natural `n >= 17`
would falsify this refutation. The kernel-checked value at `n = 17` proves
that the two sides are 935 and 937, so such a proof would contradict the
formal result.

## Evidence

- Lean module:
  `D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- The recorded kernel type-checking time is 0.00852 seconds, with maximum
  resident set size 1,438,793,728 bytes for the profiled Lean process.
- The orchestrator and probe independently evaluated the exact integer
  square-root recurrence through `n = 1000`. The literal recurrence was violated at
  every index `17 <= n <= 1000`, for 984 violations out of 984 inputs.

The bounded computations beyond index 17 are supporting evidence only. The
formal result uses the single explicit instance `n = 17` and makes no claim
about any other index.

**Sign reading (orchestrator-verified numerics, not formalized).**

The entry's own odd and even closed forms imply
`a(n) = a(n-2) + a(n-4) - 1`. This sign-corrected reading holds for every
`17 <= n <= 32`, then fails at `n = 33`: `a(33) = 43873`, whereas
`a(31) + a(29) - 1 = 43874`. It has 69 failures over `17 <= n <= 399`.
The odd closed form fails at `m = 16`, where it gives 43874 instead of
`a(33) = 43873`; the even closed form fails at `m = 19`, where it gives
236399 instead of `a(40) = 236398`. Thus the refutation does not merely
refute a typographical sign error. The formal `claim` remains the literal
source text recorded before the proof was constructed.

## Triage

`theorem`. The certified instance at `n = 17` refutes the literal universal
recurrence. It asserts no corrected recurrence, no closed form, and no claim
about any other value of `n`.

## ASSUMED-UNVERIFIED

OpenAlex, Semantic Scholar, and grep.app were rate-limited, GitHub code search
was unauthenticated, and individual OEIS revision pages returned HTTP 403.
The literature search is bounded and does not establish exhaustive coverage
or publication priority. The sign-corrected recurrence and the closed-form
failures are numerical checks only and are not formalized here.
