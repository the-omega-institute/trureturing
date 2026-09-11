---
slug: oeis-a146557-collinear-triple-divisibility
bibkey: oeis2025a146557
doi: null
url: https://oeis.org/A146557
triage: theorem
motivation_gids:
  - D5/S3/Factorization/CollinearTripleTranslationOrbits
---

# The A146557 collinear triple divisibility conjecture

## Problem

Peter Bala's July 24, 2025 comment conjectures that n squared divides a(n)
when three does not divide n. Here a(n) counts unordered collinear triples
in (ZMod n) squared whose first coordinates, and second coordinates, are
pairwise distinct. Collinearity means the difference determinant is zero.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection of the entry
on September 8, 2026 found the statement still labelled Conjecture.

## Gap

The implementation brief reports no independent proof in its public-index
search. The mathematical obligation is to show that the translation action
on the admissible unordered triples is free when three is coprime to n.

## Route

Translation preserves the coordinate restrictions and the determinant.
If translation by t stabilizes a three-element set S, its element sum is
both sum(S) and 3t+sum(S). Cancellation gives 3t=0. Coprimality makes three
a unit modulo n, so t=0. The free-action product equivalence decomposes the
configuration set as its orbit quotient times the translation group, whose
cardinality is n squared.

The brief instead derives 3t=0 by observing that a nonzero stabilizing
translation permutes the three elements without fixed points and therefore
is a 3-cycle. Both arguments establish the same torsion obstruction.

## Falsifier

A positive modulus not divisible by three for which the defined unordered
configuration count is not divisible by n squared would contradict the theorem.

## Evidence

- Module: `D5/S3/Factorization/CollinearTripleTranslationOrbits.lean`.
- Theorem: `square_dvd_card_collinear_triples`.
- `Triple n` is a subtype of `Finset (Point n)`, with cardinality exactly three.
- The proof has no finite search cutoff or computational enumeration premise.
- The source has a(3)=6, so the restriction on n cannot simply be omitted.

## Triage

`theorem`. The normalized universal assertion is proved. No claim is made
that every multiple of three fails divisibility; that converse is not needed.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The brief's literature search
does not exhaust private or unindexed sources. External OEIS identification
is checked by reading the entry, not by a theorem about its website.
