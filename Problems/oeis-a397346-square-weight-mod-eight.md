---
slug: oeis-a397346-square-weight-mod-eight
bibkey: hanna2026a397346
doi: null
url: https://oeis.org/A397346
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity
---

# A397346: square-weight congruence

## Problem

Paul D. Hanna's OEIS A397346 NAME is the formal equation
A(x)=exp(x+Sum_{n>=2}(2*n^2-1)*a(n)*x^n/(2*n^2)).
Its first COMMENT is the single target of this dossier:

> Conjecture: a(n) == [4,2,0,2] repeating (mod 8) for n >= 2.

## Motivation

First-tier 2026 conjecture. This is one endpoint of the shared integer
square-weight family; A397242's parity endpoint already exists and is reused.

## Gap

On 2026-09-09 the continuation worker read the source JSON and all direct
A references named in Library/Words/oeis2026triage0909.md. Target comments
remain conjectural and the fields read contain no target proof link.
The bounded search details and failures are in the family Library note.

## Route

Define b(q,0)=0, b(q,1)=1 and, for n>=2,
b(q,n)=q(n-1)b(q,n-1)+Sum_{2<=j<n}(q*j^2-1)(n-j)b(q,j)b(q,n-j).
Set a(q,0)=1 and a(q,n)=n*b(q,n) for positive n. All coefficients are integers.
For nonzero integer q, source_iff proves the literal rational formal
exponential equation is equivalent to f(n)=a(q,n) at every natural n;
thus existence, integrality and uniqueness are established, not assumed.

Strong induction gives b(2,n)=6 in ZMod(8) when n=3 modulo four,
and 2 otherwise, for n>=2. Endpoint separation reduces the interior sum to
2(n-2)(n-1)-4 modulo eight. Multiplying by n yields the stated cycle.

## Falsifier

An index in the stated range whose exact source coefficient violates the
quoted congruence would refute this claim. A mismatch in source_iff would
invalidate the identification with the NAME even if the recurrence passed.

## Evidence

Lean: D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.residues_q2.
Source correspondence: the same module's source_iff and generating_unique.
Own exact checks cover n<=200, the independent Fraction/log construction
through degree 30, and every term in the retrieved OEIS data field; no mismatch.
Finite checks support source fidelity; the Lean inductions prove all indices.
Gate receipts and worker artifact references are recorded in the family note.

## Triage

`theorem`. The proposed live witness was preregistered in commit bb412c5f7e
before predecessor proof probes. This continuation rechecks the existing proof.

## ASSUMED-UNVERIFIED

One continuation Codex worker under lean4; no independent review or consensus
is claimed. The core congruence proof was inherited and then recompiled by
this worker; the literal exponential bridge was rescued in mid-implementation
and reverified here. New local numerical and source-field reads are this
worker's own checks. Prior broad web-search failures are predecessor reports.
No exhaustive literature search, first-publication priority, analytic limit,
or any other conjecture in this entry is claimed. The typed resolution edge
records this repository's theorem, not an update to the external OEIS page.
