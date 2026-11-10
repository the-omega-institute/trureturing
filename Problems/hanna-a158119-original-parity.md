---
slug: hanna-a158119-original-parity
bibkey: hanna2009a158119
doi: null
url: https://oeis.org/A158119
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaA158119Parity.result
---

# Hanna's original A158119 parity conjecture

## Problem

Paul D. Hanna's OEIS A158119 conjecture states:

> Conjecture: a(m) == 1 (mod 2) iff m is a power of 2 or m=0. [Paul D. Hanna, Mar 16 2009]

Let F(X) be the original A155585 ordinary generating function over the integers, given by the formal series sum over n >= 0 of n! * X^n * product over k=1,...,n of (1+2*k*X)^(-1), with empty product 1. Let Q(X) be the unique compositional inverse with zero constant coefficient of X*F(X), and let B(X) be the original A157308 series X/Q(X), meaning the unique normalized series with B(X)*Q(X)=X. For every natural integer m >= 0 define the original unsigned-bisection A158119 coefficient a(m) as the absolute value of the integer coefficient of X^(2*m) in B(X). The event E is: for every natural integer m >= 0, a(m) is odd if and only if m=0 or there exists a natural integer j >= 0 such that m=2^j. This includes m=0 and m=1, both directions, and all indices without a finite cutoff. There is no additional analytic, combinatorial, algorithmic, resource, Lean, formalization-success or verification condition.

The entire event is preregistered in [issue #28830](https://github.com/the-omega-institute/trureturing/issues/28830).
Its UTF-8 SHA-256 is `0098c8422acd60309a9754f783bec68ae1e8bf91ed649c94bbc63dd5d1c0cfed`.
A157310 is an alias, not a second problem. The factorial/product expression is
an ordinary generating function; the separately listed exponential generating
function `exp(X)/cosh(X)` does not replace it.

## Motivation

The assertion determines exactly which coefficients of the original unsigned
even bisection are odd, at every index. A finite prefix, one implication,
a sibling weight, or a conditional source-identification result cannot settle it.

## Gap

The pinned source and related literature are identified in
`Library/RecurrenceAlgebraic/hanna2009a158119.md`. Within that bounded corpus no explicit
supplier of the complete original-square-weight assertion was found.
The closest inspected prior proves the quartic-weight A338634 analogue and
gives general common-opener/matching background; it is related prior work.
No global priority or absence claim follows from the bounded search.

## Route

Reduction modulo two sends each denominator factor to one and kills `n!`
for `n >= 2`, so `F = 1+X` over `ZMod 2`. The original quotient identity
`B*Q=X` then gives `B=1+Q` and `Q+Q^2=X`. Uniqueness of unit-linear reversion
identifies the reduced `Q` with the existing Catalan series. Its established
binary support criterion, followed by the original even bisection and
invariance of oddness under integer absolute value, proves the full iff.
The constant coefficient gives the zero case.

## Falsifier

A natural `m` for which the original coefficient's absolute value is odd
without `m=0` or `m=2^j`, or is even at one of those indices, contradicts the
assertion. Failure of a proof attempt is not such a counterexample.

## Evidence

The exact formal owners are
`D5/S1/Recurrence/Algebraic/HannaA158119Parity.lean` and its matching Blueprint
Scribe. `result : claim` quantifies over every natural `m` with both directions,
including zero and one. The definitions `summand`, `F`, `Q`, `B`, and `a`
retain the original factorial/product OGF, reversion and unsigned bisection.
`quotient_equation` is consumed by `Q_mod_two`.

## Triage

Tier 1 external named conjecture; resolution `proved` is bound only to
`D5/S1/Recurrence/Algebraic/HannaA158119Parity.result`.
All public and private theorem proof shapes are `bind-only`; the helpers
are consumed in the result's proof. Admission is solely
`open-problem-resolution` under issue #28830, with no new-method or
escape-witness credit. Utility is `none`: the proof is an unbounded symbolic
argument, not bounded enumeration, a checker, a numerical reduction or a
certified finite instance.

### What the settlement shows

Proved by `result`: the original unsigned bisection has odd terms exactly at
zero and powers of two. The mechanism is the original OGF's mod-two collapse
and the existing Catalan support theorem. The argument includes all indices;
there is no range bound to extend. The alias A157310 refers to the same event.
No additional neighbouring conjecture, general weight theorem, analytic
cumulant identification, or consequence for other source questions is asserted.
Such extensions remain open here. The quartic sibling already has the cited
prior treatment and is not counted again.

## ASSUMED-UNVERIFIED

Global priority and exhaustive literature coverage are unverified. The source
history endpoint returned HTTP 403 and several provider searches were blocked
or unusable. The independent bounded screening inspected 18 path snapshots
(4+2+4+8), not 22 revisions. These limits do not weaken the mathematical event.
