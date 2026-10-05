---
slug: mathar-2012-a113409-recurrence
bibkey: mathar2012a113409
doi: null
url: https://oeis.org/A113409
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.result
---

# Mathar's recurrence for OEIS A113409

## Problem

OEIS A113409 is named "A transform of the central binomial coefficients A001405."
Its FORMULA field defines the sequence literally:

> a(n) = Sum_{k=0..floor(n/2)} C(n-k, k)*C(k, floor(k/2)).

The conjecture in the same field is:

> Conjecture: (n+2)*a(n)-2*(n+1)*a(n-1) +(n-4)*a(n-2) +2*a(n-3) +4*(2-n)*a(n-4)=0. - _R. J. Mathar_, Nov 07 2012

Preregistration issue #13334 fixes the nonnegative-index domain: every natural
`n >= 4`. The binomial sum and its indices are natural numbers; the displayed
recurrence is evaluated in the integers. Its statement is `claim`, and
`D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.result` proves it.

## Motivation

The recurrence gives an unbounded exact relation among five consecutive values
of the sequence defined by the source sum.

## Gap

Issue #13334 records a tier-1 formula-field conjecture and a bounded literature
search: the candidate search seat reports no proof in arXiv, MathDB, or
`google-deepmind/formal-conjectures`. The recorded OEIS source has the conjecture label and literal formula.
These readings establish
`not-found-in-searched-scope`, without an exhaustive novelty or priority claim.

## Route

Write `b(k) = C(k, floor(k/2))` and extend the triangular transform to
`T_b(n) = sum_{k=0..n} C(n-k,k)b(k)`; the added terms vanish. Pascal's identity
and its weighted version control `T_c` and
`W_c(n) = sum_{k=0..n} k C(n-k,k)c(k)` for arbitrary integer-valued `c`.
The even and odd expressions for `b` reduce its two-step recurrence to the
central-binomial recurrence. Transforming that relation and eliminating the
shifted weighted sums produces the successive difference of the desired
five-term expression. Its value at zero is zero, and induction proves the
expression is zero at every forward-shifted index. The vanishing tail then
identifies `T_b` with the literal source sequence.

## Falsifier

A natural `n >= 4` whose literal binomial sum violates the displayed integer
recurrence would contradict `result`.

## Evidence

The canonical mathematical source is
`D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.lean`.
Its public surface consists of `a`, `claim`, and `result : claim`; every
auxiliary proposition is a local proof term inside `result`.
The corresponding Blueprint describes all three declarations and attaches a
`Proved` resolution claim to `result`.

## Triage

Tier 1 external named conjecture, preregistered in #13334.
`admission_basis: open-problem-resolution (#13334; Proved)`; utility `none`.

### What the settlement shows

- **Proved in `D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.result`:**
  the exact recurrence holds for every natural `n >= 4`, with no additional
  hypothesis on the sequence defined by the source sum. The decisive mechanism
  is the elimination of the weighted transform followed by induction in the
  local `tr_recurrence` proof.
- **Proved inside that result:** the transform extension has a vanishing tail,
  and its weighted Pascal identities supply the difference relation used by
  the induction. These local identities describe the argument's scope; they
  are not separate exported settlement theorems.
- **Open:** an extension below index four requires a specified convention for
  negative sequence indices. The source's generating-function equation and
  asymptotic formula remain separate assertions. This module proves neither
  those assertions nor a dependency from this recurrence to other source
  results, and settles no additional named conjecture.

## ASSUMED-UNVERIFIED

Worldwide novelty, publication priority, and the absence of an independent
proof outside the recorded literature-search scope are unverified. A direct
source request returned HTTP 403; source fidelity is supported by the
preregistration and the recorded successful OEIS source verification.
