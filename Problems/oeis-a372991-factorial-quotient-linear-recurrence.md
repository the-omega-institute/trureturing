---
slug: oeis-a372991-factorial-quotient-linear-recurrence
bibkey: kimberling2024a372991
doi: null
url: https://oeis.org/A372991
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence
---

# Mathar's linear recurrence for the A372991 factorial-quotient sequence

## Problem

OEIS A372991 NAME (Clark Kimberling, Jul 15 2024):

> a(n) = (2n)!/(a(n-1)*a(n-2)), where a(0)=1, a(1) = 1.

FORMULA (for n ≥ 3):

> Conjecture D-finite with recurrence a(n) -2*n*(2*n-1)*a(n-3)=0. - R. J. Mathar, Jul 16 2024

## Motivation

This is a first-tier recent OEIS conjecture from 2024. The target is the
universal recurrence, with KPI = open problems resolved.

## Gap

The supplied search reported no proof found: the search seat read the OEIS
entry and revision history on 2026-09-08 and searched arXiv, MathOverflow,
and GitHub by identifier. This Stage-B seat had no network access and did
not independently repeat those readings or searches. No exhaustive
literature or first-publication priority claim follows from that scope.

## Route

Define the sequence over the rationals, so division does not assume
integrality. Two-step induction proves positivity. For n ≥ 3, the consecutive
triple products a(n)a(n−1)a(n−2) = (2n)! and
a(n−1)a(n−2)a(n−3) = (2n−2)! share two positive factors. Cancellation gives
a(n)/a(n−3) = 2n(2n−1), equivalently Mathar's recurrence. Integrality follows
by induction along residue classes mod 3, starting from a(0)=1, a(1)=1,
and a(2)=24; the Lean proof implements this as strong induction on n.

## Falsifier

A counterexample index n ≥ 3 for the defined sequence with
a(n) ≠ 2n(2n−1)a(n−3) would contradict the assertion. The orchestrator's
exact check is supporting evidence only, not a substitute for the unbounded
proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.lean`.
- Main theorem: `mathar_recurrence`.
- Actual companions: `a_pos`, `triple_product`, and `a_integral`.
- The requested names `mathar_recurrence_one`, `altRowSum_succ_sub`, and
  `fib_cassini_two` are not declarations in this module; they are not claimed
  as proved companions or used as evidence for this resolution.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), exactly as
  reported for all four public theorems in the implementation seat's receipt.
- The resolution claim is attached only to `mathar_recurrence` in the Scribe
  source; finite checks do not carry the universal assertion.

## Triage

`theorem`. The formal proof establishes the displayed polynomial-coefficient
linear recurrence for every n ≥ 3. It also proves natural-number integrality
of every rationally defined term.

## ASSUMED-UNVERIFIED

The verbatim NAME and FORMULA quotes, attribution, and dates were supplied
by the orchestrator. The OEIS revision history was read by the search seat,
not this seat. The supplied literature scope was the OEIS entry and revision
history read on 2026-09-08 plus identifier searches on arXiv, MathOverflow,
and GitHub. This seat had no network access; later edits, literature outside
that scope, and first-publication priority were not independently checked.
Source-to-Lean identification is not a kernel-checked fact. The std3 report
and prior compilation were supplied evidence; Stage B did not rerun them.
