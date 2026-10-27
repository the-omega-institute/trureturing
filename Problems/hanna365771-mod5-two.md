---
slug: hanna365771-mod5-two
bibkey: hanna2023a365771
doi: null
url: https://oeis.org/A365771
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/HannaA365771Two
---

# Hanna's second congruence for A365771

## Problem

OEIS A365771 revision 23, Comments, states:

> Conjectures: given A033042 is the sums of distinct powers of 5, then
> (2) a(5*A033042(n) + 1) == 2 (mod 5) for n > 0,

Preregistration: [#18657](https://github.com/the-omega-institute/trureturing/issues/18657).

### Statement echo

Every positive $m$ in A033042 satisfies $a(5m+1)\bmod5=2$.
The sequence and digit predicate are exactly `D5.S1.Recurrence.Residue.HannaA365771.a`
and `D5.S1.Recurrence.Residue.HannaA365771.InA033042`. The claim uses natural-number arithmetic.

## Motivation

This is one of the three residue assertions in A365771; the family dossier is
[hanna365771-mod5.md](hanna365771-mod5.md), and the source note is
`Library/Digit/hanna2023a365771.md`.

## Gap

The source labels the assertion a conjecture. The preregistration records the source and literature screen.
Search completeness and publication priority are `ASSUMED-UNVERIFIED`.

## Route

The same-delivery `HannaA365771.digits_step` and `HannaA365771.residue_classification`
supply the digit decomposition and the residue. The shared module is not a previously frozen dependency.
The positive integer $5m+1$ has remainder one and quotient $m$ upon division by five.
Its digits therefore satisfy the same zero/one condition, and the classification gives residue two.

## Falsifier

An input satisfying the claim's hypotheses with a different residue would refute the assertion.
A source-to-definition mismatch would invalidate fidelity.

## Evidence

Kernel-checked settling declaration: `D5.S1.Recurrence.Residue.HannaA365771Two.result`.
The module's admission basis is `open-problem-resolution (#18657; Proved)` and utility is `none`.
Its Scribe records a Proved resolution of this dossier.
Four-slot escape registration for this result is unfinished under
[issue #22018](https://github.com/the-omega-institute/trureturing/issues/22018).
No successful Reg registration is claimed.
The family dossier contains the immutable experiment reference and the finite computed readings.

## Triage

- **Proved:** kernel-checked `HannaA365771Two.result` proves the exact claim.
- **Proved:** the complete positive-index classification and multinomial indicator are the
  kernel-checked `HannaA365771.residue_classification` and private `HannaA365771.M_mod`.
- **Computed:** the family dossier's pinned checker passes through $n=6000$ and checks
  the scaled identity for $1\leq n<3000$; this is finite evidence.
- **Open:** higher powers of five, other primes and the unbounded stronger valuation comparison.

### What the settlement shows

The digit classification determines the residue for every input of this assertion;
no numerical upper bound is a hypothesis. The other two congruences have their own
kernel-checked results in the same family. The stronger valuation comparison is not asserted in Lean.

## ASSUMED-UNVERIFIED

Literature-search completeness, publication priority and source-to-definition identification
retain the boundaries stated in the family dossier.
