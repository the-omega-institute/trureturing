---
slug: granvik-2024-a292273-real-part
bibkey: granvik2024a292273
doi: null
url: https://oeis.org/A292273
triage: theorem
motivation_gids:
  - D5/S3/Arith/Mobius/GranvikMobiusRealPart.result
---

# Granvik's A292273 real-part identity

## Problem

Mats Granvik, OEIS A292273, revision 24, Jul 06 2024:

> For odd n: a(n) = 0, and for even n: a(n) = -mu(n), where mu is Moebius function (A008683).

> Conjecture: a(n) = Re(A008683(n)*(i^n)). - _Mats Granvik_, Jul 06 2024

The offset is one. The assertion concerns every positive integer, with no
upper bound. Here mu is the standard integer Mobius function and i is the
ordinary complex imaginary unit.

## Motivation

The declaration `D5/S3/Arith/Mobius/GranvikMobiusRealPart.result` proves
exactly this arithmetic identity. The necessary public definition `a`
uses the two literal parity clauses. Its total extension to natural index
zero does not extend the theorem's positive-index conclusion.

## Gap

Preregistration: https://github.com/the-omega-institute/trureturing/issues/25889#issuecomment-6591253163.
The source and bounded literature qualification are in
`Library/Factorization/granvik2024a292273.md`. No exact prior answer was
found in the inspected scopes; global absence is not established.

## Route

Reduce the arbitrary natural exponent modulo four. Odd residues give zero
real part. Residue two gives minus mu(n). For residue zero, four divides n,
so n is not squarefree and mu(n) vanishes. The proof directly reuses the
pinned Mathlib squarefree and complex-power results and normalizes the
resulting expressions.

## Falsifier

A positive index violating the identity would refute the source assertion.
A changed Mobius function, finite cutoff, extra squarefree hypothesis,
missing parity case or substituted trajectory claim would invalidate the
source correspondence.

## Evidence

The Lean theorem quantifies `n : Nat` and `0 < n`, with conclusion
`(a n : Real) = ((ArithmeticFunction.moebius n : Complex) * Complex.I ^ n).re`.
The integer-to-real and integer-to-complex coercions preserve the source
values. Its Scribe carries the typed `Proved` resolution claim.
The Reg mirror registers the whole positive-index law with a
source-equivalence bridge, real-part readout, whole-family intervention
and observational dependence; continuation is unknown.

## Triage

Tier 1: a named small conjecture published in 2024, with bounded source and
literature qualification in the preregistration. `admission_basis:
open-problem-resolution`; `result` has `proof_shape: bind-only`, and the
only other D5 declaration is its necessary source definition `a`.
`utility: none`: the universal symbolic proof partitions an arbitrary
index into residue classes and performs no bounded search or certification.

**Proved:** the complete positive-index arithmetic identity. The decisive
mechanism is Mobius vanishing when four divides the index, together with
periodicity of powers of i. The proof adds no new generic Mathlib theorem.

**Open scope:** no Collatz trajectory interpretation or trajectory
termination conclusion is proved. No source claim about those topics is
changed by this identity. Further identities or generalizations require
separate statements and qualification.

## ASSUMED-UNVERIFIED

Absence of an earlier published proof outside the inspected scopes remains
ASSUMED-UNVERIFIED. No priority or exhaustive novelty claim is made.
