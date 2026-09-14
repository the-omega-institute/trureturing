---
slug: oeis-a395833-diagonal-exponent-self-divisibility
bibkey: hanna2026a395833div
doi: null
url: https://oeis.org/A395833
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility
---

# OEIS A395833: diagonal-exponent self-divisibility

## Problem

The Library note quotes the NAME and divisibility conjecture verbatim:

> G.f. A(x) satisfies [x^n] A( x/A(x)^(2*n-1) ) = 0 for n > 1. Conjecture: (2*n-1) divides a(n) for n >= 1.

The supplied local OEIS source identifies the entry and its separate conjecture:

```text
%N A395833 G.f. A(x) satisfies [x^n] A( x/A(x)^(2*n-1) ) = 0 for n > 1.
%C A395833 Conjecture: (2*n-1) divides a(n) for n >= 1.
%C A395833 Conjecture: a(n) == 0 (mod 3) for n >= 2.
%A A395833 _Paul D. Hanna_, May 07 2026
```

The problem resolved here is the divisibility clause only: `(2*n-1)` divides
`a(n)` for every `n >= 1`. The separate modulo-three clause is outside this claim.
The sequence is the unique normalized integer series with constant and linear
coefficients one satisfying the displayed vanishing-diagonal equation.

## Motivation

This is a first-tier OEIS conjecture from 2026 (the supplied AUTHOR line is
May 07 2026). KPI = open problems resolved. The general theorem covers every
positive natural slope; the A395833 specialization is one resolution, not an
additional independent result.

## Gap

No proof was found in the scope reported by the search seat: the OEIS entry and
revision history read on 2026-09-09, and identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not repeat
those searches. This is a bounded search report, not a priority certificate.
The formal gap is exponent-weighted divisibility of the triangular summands.

## Route

Write `e(n) = d*(n-1)+1` and use the frozen construction
`A = NegativePowerDiagonalModPrime.generatingSeries (d+1)`.
Its public `generating_equation` and `generating_unique` identify the sequence;
these declarations belong to the frozen construction module, not this module.
Expanding the vanishing diagonal writes the nth coefficient as a negative sum
of smaller coefficients times inverse-power coefficients `c`. The frozen
`DiagonalVanishingIndexDivisibility.power_coefficient_identity` implies
`e(n) | (n-m)*c`. The private `affine_summand_dvd` uses
`e(m) = e(n)-d*(n-m)` and the induction hypothesis to show that `e(n)` divides
each summand. Strong induction proves `exponent_self_divisibility`; setting
`d=2` proves `hanna_conjecture_a395833`.

The header records generality I; the proof imports the frozen D5 module
`DiagonalVanishingIndexDivisibility`, which supplies the derivative engine and
transitively the construction. The implementation seat re-established the
inaccessible private substitution expansion, while reusing the public engine.
`affine_summand_dvd` is a private prerequisite, not an oddness corollary.
No modulo-four classification, double-composition contraction, or polynomial
certificate is asserted by this module; those supplied Route instructions do
not describe the delivered Lean proof.

## Falsifier

An index `n >= 1` of the specified normalized sequence for which `(2*n-1)` does
not divide `a(n)` would falsify the OEIS divisibility assertion. More generally,
a positive slope and positive index violating `e(n) | a(d+1,n)` would falsify
the general theorem. The orchestrator's exact numerical check is supporting
evidence only; its data and exit code were not independently checked here.
The supplied 39-position modulo-four check does not test this divisibility theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility.lean`.
- Main theorem: `exponent_self_divisibility`.
- Public companion: `hanna_conjecture_a395833`, the slope-two specialization.
- Private live prerequisite: `affine_summand_dvd`; it is not a separate result.
- Axiom closure reported by Stage A for both public theorems: std3
  (`propext`, `Classical.choice`, `Quot.sound`).
- Frozen construction and uniqueness are reused, not claimed as new results.

## Triage

`theorem`. The proof resolves the universal divisibility assertion, with one
specialization identifying A395833.

A395833 carries two separate conjectures. This resolution claim covers ONLY the
divisibility conjecture `(2*n-1) divides a(n) for n >= 1`. The entry's other
conjecture, `a(n) == 0 (mod 3) for n >= 2`, was settled earlier by the frozen
module `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime` and is quoted
above only as part of the verbatim source text; it is NOT asserted here and is
NOT counted again. The delivered module states the same boundary in its
docstring.

## ASSUMED-UNVERIFIED

Quotes are supplied by the orchestrator through the Library note and local
`oeis-A395833.src`; this seat did not retrieve OEIS. The revision history was
read by the search seat, not this seat. Literature scope is the entry, revision
history, and identifier searches on arXiv, MathOverflow, and GitHub reported
above; search completeness and first-publication priority are not verified.
The multi-entry quotations, 2016–2018 author dates, and “All terms appear to be
odd.” in the dispatch are absent from the lane's source and are not attributed
to A395833 here. Source-to-Lean identification is not an OEIS provenance proof.
