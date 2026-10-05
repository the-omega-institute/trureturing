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
- **Computed:** the literal sum equals the OEIS data for every `0 <= n < 20`
  (20 exact integer matches), using the fetched b-file
  `https://oeis.org/A113409/b113409.txt`.
- **Computed:** the displayed recurrence residual is zero for every
  `4 <= n < 40` (36 exact integer residuals), evaluated on the literal sum.
  Both computations use
  `python3 /Users/auric/.sshx/86bc0b314415216d22d436a5/attempt-1/check-a113409.py`,
  exit 0; script SHA-256
  `f9b2d9148205cf8880fe2613013bd47616f619d565338ec8993b39011ba92376`.
  These finite checks do not establish an unbounded statement.
- **Open to kernel verification in this delivery (derived, not kernel-verified):**
  the generating-function equation `HY² = V²` from #13334. Its definitions are
  `G(x) = sum_{n>=0} a(n)x^n`, `H = 1-2x+x²-4x⁴`,
  `V = 1-x+2x²`, and `Y = 1+2x²G`. The issue derives the equation by
  substituting `w = x²/(1-x)` into
  `(1-4w²)(2wB(w)+1)² = (1+2w)²`, where
  `B(w) = sum_{k>=0} C(k, floor(k/2))w^k` and
  `G(x) = (1-x)⁻¹B(x²/(1-x))`. This is the issue's generating-function
  derivation, not a consequence kernel-verified by `result`.
- **Open in this delivery:** Kotesovec's asymptotic
  `a(n) ~ 2^(n+3/2)/sqrt(3πn)`, as stated in the OEIS A113409 FORMULA
  field and attributed there to Vaclav Kotesovec. The delivered `result`
  supplies no proof of this asymptotic.
- **Open:** an extension below index four requires a specified convention for
  negative sequence indices. This module proves no dependency from the
  recurrence to other source results and settles no additional named conjecture.

## ASSUMED-UNVERIFIED

Worldwide novelty, publication priority, and the absence of an independent
proof outside the recorded literature-search scope are unverified. A direct
source request returned HTTP 403; source fidelity is supported by the
preregistration and the recorded successful OEIS source verification.
