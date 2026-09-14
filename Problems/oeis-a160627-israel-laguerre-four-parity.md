---
slug: oeis-a160627-israel-laguerre-four-parity
bibkey: sloane2018a160627
doi: null
url: https://oeis.org/A160627
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/IsraelLaguerreFourParity
---

# Laguerre(n, 4) has odd numerator and denominator

## Problem

OEIS A160627, NAME (`%N`, verbatim):

> Numerator of Laguerre(n, 4).

Robert Israel's COMMENT conjecture (`%C`, verbatim):

> Conjecture: all terms are odd. - _Robert Israel_, Mar 29 2018

OEIS A160628, NAME (`%N`, verbatim):

> Denominator of Laguerre(n, 4).

Robert Israel's COMMENT conjecture (`%C`, verbatim):

> Conjecture: all terms are odd. - _Robert Israel_, Mar 29 2018

The literal proved statement defines
`L(n) = sum_{k=0}^n C(n,k)(-4)^k/k!` in the rationals and proves
`forall n : Nat, Odd (L n).num and Odd (L n).den`. Here `num` and `den`
are the numerator and denominator of the reduced rational value. The
definition is the explicit binomial sum for the classical Laguerre polynomial
at `x=4`; it does not use a Mathlib Laguerre polynomial API.

No value other than `x=4`, property beyond reduced numerator and denominator
parity, other A160627 or A160628 comment, or priority claim is included.

## Motivation

The two sequences separately record the reduced numerator and denominator of
the same rational polynomial value. A single universal theorem settles both
of Israel's parity conjectures and identifies the common 2-adic reason for
their observed oddness.

## Gap

On 2026-09-15, the probe read all 12 revisions of A160627 and all 14 revisions
of A160628. Both conjecture comments had remained present since 2018, and no
OEIS revision supplied a proof or refutation. The arXiv web search returned
zero results; the arXiv export API returned HTTP 503. OpenAlex returned zero
results, and MathOverflow returned zero results. GitHub returned zero exact
phrase matches; identifier-only hits were generator data in `joeis` and
`loda`. A search of pinned Mathlib found the required valuation lemmas but no
matching Laguerre parity theorem.

These checked surfaces do not establish exhaustive literature coverage, and
no priority claim is made.

## Route

1. For every nonconstant summand, combine
   `padicValNat_factorial_lt_of_ne_zero` with `padicValRat.mul`,
   `padicValRat.div`, `padicValRat.pow`, `padicValRat.of_nat`, and
   `padicValRat.neg` to show that its 2-adic valuation is positive.
2. Apply `padicValRat.sum_pos_of_pos` to the tail and
   `padicValRat.add_eq_of_lt` to the constant term plus the tail, obtaining
   2-adic valuation zero for `L(n)`.
3. Rewrite through `padicValRat_def`. Use `Rat.reduced` and
   `dvd_iff_padicValNat_ne_zero` to exclude a factor of two from both the
   reduced numerator and denominator, then apply the integer and natural
   parity equivalences.

The proof is bind-only over these pinned Mathlib facts: the remaining steps
are their instantiation, arithmetic normalization with `omega`, and logical
projection.

## Falsifier

Any natural `n` for which either reduced component of the explicit rational
sum is even would contradict `result`. A mismatch between that sum and the
Laguerre value represented by the two OEIS sequences would instead falsify
the source-to-definition correspondence, not the kernel theorem.

## Evidence

- Lean module: `D5/S3/ArithSums/IsraelLaguerreFourParity.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 7.54 seconds, type checking
  16.8 milliseconds, and maximum resident set size 1,627,226,112 bytes.
- Deleting the sole direct Mathlib import makes the module fail to compile;
  restoring it gives a zero-exit single-file build.
- The first seven reduced pairs are `(1,1)`, `(-3,1)`, `(1,1)`, `(7,3)`,
  `(1,1)`, `(-13,15)`, and `(-83,45)`, matching the OEIS data.
- The orchestrator's independent exact `Fraction` recomputation found zero
  even components through `n=300` and agreed with `sympy.laguerre` through
  `n=60`. The probe found zero even components for `n<400`.
- The bounded calculations support fault detection only; the Lean theorem
  carries the universal statement.

## Triage

`theorem`. Israel's two parity conjectures are proved for every natural `n`;
the resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

The bounded scans do not establish the universal statement. Literature
completeness outside the checked OEIS histories, arXiv, OpenAlex,
MathOverflow, GitHub, pinned Mathlib, and repository searches is unverified;
no exhaustive literature or priority claim is made. The finite numerical
agreement does not independently establish that every OEIS term uses the
same normalization as the explicit rational sum.
