---
slug: oeis-a102086-row-polynomial
bibkey: kurkov2026a102086
doi: null
url: https://raw.githubusercontent.com/oeis/oeisdata/07c3ba2e0a0dab01600c762da7c11349d5de8548/seq/A102/A102086.seq
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/KurkovA102086RowPolynomial.result
---

# Kurkov's A102086 row-polynomial conjecture

## Problem

Paul D. Hanna's OEIS A102086 NAME and Mikhail Kurkov's FORMULA conjecture
specify a lower triangular integer matrix T and a polynomial table P:

\[
T(n,n)=n+1,\quad
T(n,k)=\sum_{k\le j<n}T(n-1,j)T(j,k)\quad(k<n),\quad T(n,k)=0\quad(n<k),
\]

\[
P(a,a)=X^a,\quad P(a,0)=1,\quad
P(a,b)=P(a,b-1)+(b+1)P(a-1,b)\quad(0<b<a),
\]

with P(a,b)=0 for b<0 or b>a. Here a,n,k are natural numbers, b is an
integer, and the polynomials lie in Z[X]. The complete question asserts
existence of both tables and, for every source pair and every n>=0,

\[
\sum_{k=0}^{n}T(n,k)X^k=P(n+1,n).
\]

The [source note](../Library/RecurrenceAlgebraic/kurkov2026a102086.md)
retains the exact quotation, source pin, attribution and CC BY-SA 4.0
license. [Preregistration #23496](https://github.com/the-omega-institute/trureturing/issues/23496)
fixes the full event and prospectively nominates the operator-shift route.

| Source clause | Lean counterpart |
| --- | --- |
| T:N x N -> Z, zero above diagonal, diagonal n+1 | `IsSourceTriangle` first two conjuncts |
| Matrix-square entry in row n-1, for k<n | `IsSourceTriangle` third conjunct, `Finset.Ico k n` |
| P:N x Z -> Z[X], including negative exterior indices | `IsSourcePolynomialTable`, integer second argument |
| X^a diagonal, zero-column 1, all exterior zeros | First three conjuncts of `IsSourcePolynomialTable` |
| Exact interior coefficient b+1 | Last conjunct, `C (b+1)` |
| Both tables exist; any source pair; every n including zero | All three conjuncts of `claim` and theorem `result` |

## Motivation

This is a tier 1 attributed OEIS FORMULA conjecture. The source's conjecture
label is retained as a source fact. Classical support and partial results
do not count as settlement of this full event.

## Gap

No complete prior target theorem was identified in the inspected repository,
pinned Mathlib, related OEIS tables or Petrov's scalar inversion answer.
The preregistration discloses inaccessible full texts and citation-service
limits. MathDB coverage at the correct mathdb.com domain is
ASSUMED-UNVERIFIED. These bounded readings establish no global priority.

## Route

Construct P independently using the decreasing measure a+b, then extend by
zero at integer exterior indices. Put R_j=P(j+1,j) and define the Z-linear
operator L(X^j)=R_j by finite extension. Prove L(P(a,b))=P(a+1,b) on 0<=b<=a
by row and column induction, including the base and diagonal boundaries.
The source recurrence implies

\[
R_{n+1}=L(R_n)+(n+2)X^{n+1},\qquad
L(R_n)=\sum_{j=0}^{n}[X^j]R_n\,R_j.
\]

The coefficient bound above degree j makes the extracted recurrence exactly
the matrix-square recurrence, with no extra terms. Thus an actual T exists.
Uniqueness of both tables and polynomial reconstruction give the full
universal identity. Mathlib's finite linear extension and coefficient APIs
are used directly; no claim of a novel general linear-algebra method is made.

## Falsifier

A source pair and a natural row violating the displayed identity refute the
claim. Inconsistent boundary prescriptions or failure to construct a source
table also invalidate the proposed nonvacuous event. A finite positive test
cannot replace the complete proof.

## Evidence

The source module and its owning Blueprint Scribe present the complete event.
Stage A does not freeze, deposit or publish it. Compilation and registration
status are supplied by the current machine evidence, independently of this
mathematical exposition.

## Triage

The decisive proposed structure is the finite operator shift; table existence,
coefficient bounds and uniqueness retain the original normalization. All rows
are in scope. Changed weights, other polynomial diagonals and scalar
specializations are separate questions; no such extension is settled here.
No further source theorem conditional on this conjecture is identified in
the pinned NAME and FORMULA fields. Cross-references do not supply such a
conditional theorem. Delivery credit requires independent semantic review,
required checks and actual merge; Stage A earns no external-problem KPI.

## ASSUMED-UNVERIFIED

The source-to-Lean correspondence and per-declaration proof shape require
independent assessment. The bounded literature screen does not certify
worldwide priority, and the disclosed MathDB/full-text gaps remain.
