---
slug: oeis-a398690-palindromic
bibkey: chapoton2026a398690
doi: null
url: https://oeis.org/A398690
triage: theorem
motivation_gids:
  - D5/S3/Analytic/OeisA398690Palindromic
---

# Palindromic numerators of OEIS A398690

## Problem

OEIS A398690 defines `A(r,q)` by its signed finite sine sum. For every
`n >= 0`, let `F_n(z) = sum_{q>=0} A(n+3,q) z^q`. Its comment says that
`F_n` has denominator `(1-z)^(n+1)` and conjectures that its numerator
is palindromic. The formal result proves that `(1-z)^(n+1) F_n(z)` is a
polynomial of degree exactly `n` and that its coefficients at `j` and
`n-j` agree for every `0 <= j <= n`.

## Motivation

Chapoton's 2026 entry explicitly labels the all-row palindromicity
assertion a conjecture. Preregistration issue #10928 fixes the source
formula, its row shift, and the universal target before this proof.

## Gap

The OEIS comment provides the rational-row claim but no proof of
coefficient reversal. The prior project triage records only finite rows.
The A107735 cross-reference uses a different even-row normalization.

## Route

Chebyshev factorization gives a product over the sine nodes. Formal
logarithmic differentiation relates its inverse power sums to the
coefficients of an odd Chebyshev polynomial. The derivative recurrence
builds a degree-bounded polynomial model in `2q+1`, with parity matching
the row. Composing with `2X+1` turns parity into reflection about `-1/2`.
A binomial-basis calculation then turns this reflection into coefficient
reversal of the generating-series numerator. The source sine sum is
identified with the model for every `q`.

## Falsifier

A row and coefficient index violating reversal for the stated sine sum
would refute the conjecture. A finite list of matching rows cannot
establish the universal claim.

## Evidence

The source definition and the quantified `result` are in
`D5/S3/Analytic/OeisA398690Palindromic.lean`. The OEIS revision and
normalization are recorded in `Library/Analytic/chapoton2026a398690.md`.
Preregistration: issue #10928. The fresh Lean report records the source
owner's `Reg/D5/S3/Analytic/OeisA398690Palindromic.lean` registration as
`declared_validated` with evidence reference
`31acfe53a65b588e9ffa2a3532b41a112d1e28b7ed36528f574b19c3fa702d49`.
Its escape residual is `open`; this does not assert inexhaustibility.
The source result and registration use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Triage

`theorem`. The result proves the all-row source conjecture.

## ASSUMED-UNVERIFIED

The source search was bounded. Mukai (2003), p. 483 was not inspected;
priority over a possible general reciprocity result there is unverified.
The claim concerns the simplified A398690 array, not the even-row
normalization of A107735.
