---
slug: oeis-a112399-morken-first-divisor-sum
bibkey: morken2026a112399first
doi: null
url: https://oeis.org/A112399/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum.result
---

# Morken's first A112399 divisor-sum conjecture

## Problem

OEIS A112399, revision 41, source timestamp
2026-09-19T09:22:12-04:00, NAME defines:

> a(n) = Sum_{k=1..n, gcd(k,n)=1} mu(k), where mu(k) = A008683(k) (the Moebius function).

Its FORMULA section attributes the first of two conjectures to Jamie Morken,
Sep 18 2026:

> a(n) = Sum_{d|n, mu(d)!=0} (Sum_{m=1..n/d, gcd(m,d)=1} mu(m)).

The question is this equality for every positive integer n. Both intervals
include their endpoints. The function mu is integer-valued and signed, with
mu(1)=1. The outer sum ranges over positive divisors of n for which mu(d) is
nonzero, and n/d is exact integer division. The right inner coprimality is
with d; the left coprimality is with n. There is no squarefree assumption on n
and no finite upper bound. The conjecture has AI-assisted provenance, which
supplies no mathematical proof. The second A112399 conjecture, also indexed
by A400203, and the A372706 product-parameter identity are excluded.

## Motivation

The identity connects a coprime Moebius partial sum to divisor-indexed partial
sums. A universal proof supplies an exact relation between these two arithmetic
representations, beyond agreement of any finite sequence prefix.

## Gap

The stated source version labels the first equality a conjecture. The bounded
source, literature and ownership qualification in research unit #25890 did not
identify a published proof of this exact question. This observation does not
establish exhaustive global absence or a priority claim. Standard facts about
Moebius multiplicativity, squarefreeness and divisor cancellation are already
available in the pinned Mathlib and are reused.

## Route

For each divisor d and positive m, express the filtered summand as
mu(d*m)*mu(d). Vanishing of mu(d) handles nonsquarefree divisors. Otherwise,
coprimality gives multiplicativity and mu(d)^2=1, while noncoprimality forces
mu(d*m)=0. Reindex the positive interval by k=d*m and exchange the finite
sums. The coefficient of mu(k) is the Moebius sum over divisors of gcd(k,n),
which is one exactly when k and n are coprime and zero otherwise. This recovers
the original left sum with precisely its source bounds and filters.

## Falsifier

A positive integer n for which the two signed sums differ would refute the
conjecture. A finite prefix or a version with an additional squarefree
assumption would not settle the stated universal question.

## Evidence

The frozen theorem
`D5/S3/Arith/MoebiusLogarithmic/MorkenFirstDivisorSum.result` has exactly the
positive-input equality above. Its two private helpers, `summand` and
`reindex`, are consumed in that proof. Its mirrored Reg source registers the
original entire positive-input proposition through source equivalence. The
Scribe theorem carries the typed `OpenProblemResolutionClaim` for this dossier.
The accepted axiom closure is `Classical.choice`, `Quot.sound` and `propext`.

## Triage

Proved: the whole first equality for every positive natural number, with
integer Moebius values, inclusive intervals and positive divisors. The proof
uses the squarefree/multiplicative summand identity, multiplication reindexing
and cancellation over divisors of a gcd; it does not require n to be
squarefree. These are applications and finite-sum compositions of known
arithmetic facts. The result and both live private helpers have
`proof_shape: bind-only`; admission is the named external
`open-problem-resolution` exception, with `utility: none`, rather than a claim
of new generic arithmetic.

Unresolved here: an extension to n=0, other arithmetic weights, analytic
bounds or optimality assertions, the second A112399/A400203 conjecture and the
A372706 identity. No such generalization or neighboring question follows as
a delivered claim from this theorem. No further source assertion depending
on this first identity is established by the result. No finite numerical
experiment substitutes for the universal proof.

## ASSUMED-UNVERIFIED

Exhaustive global absence of an earlier published proof, research priority,
and all uninspected source history remain unverified. The official source
identity, revision and attribution are bounded source readings, and the
AI-assisted provenance is disclosed from the qualification record rather
than inferred from an official assistance field. The source's conjecture
label is distinct from the kernel-checked theorem. The dossier and typed
binding do not certify independent final review, required CI, merge or dev
synchronization.
