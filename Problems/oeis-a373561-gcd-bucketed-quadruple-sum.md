---
slug: oeis-a373561-gcd-bucketed-quadruple-sum
bibkey: oeis2024a373561
doi: null
url: https://oeis.org/A373561
triage: theorem
motivation_gids:
  - D5/S3/Factorization/A373561
---

# The A373561 divisor-bucketed quadruple sum

## Problem

Three indices run over the interval from one to a modulus and contribute the
quantity `x^2 + y^2 - z^2`. A fourth index selects, for each triple, only
those whose greatest common divisor with the modulus equals it. Mats Granvik
conjectured on June 10, 2024 that the resulting fourfold sum equals the cube
of the modulus times the sum of the first squares.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection on September 9,
2026 found the statement still labelled Conjecture, added at revision 17 with
no later revision converting it to a theorem.

## Gap

The entry already prints the target sequence as the square-sum sequence scaled
by a square, but that only names the right-hand side. What is missing is the
proof that the left-hand fourfold sum with its divisor condition reduces to
the plain threefold sum, and the searched indexes returned no such proof.

## Route

The divisor condition sorts rather than restricts. For a positive modulus the
divisor of any summand with that modulus lies between one and the modulus, so
each triple falls into exactly one class and summing over classes returns the
threefold sum. The summand can vanish or be negative; the absolute value
handles the sign, and a vanishing summand still lands in a legitimate class
because the divisor of zero with the modulus is the modulus.

What remains is a square-sum computation. The two positive squares each
contribute a full square sum scaled by the square of the interval length, and
the negative square cancels one of them, leaving that square times a single
square sum. The printed closed form then follows from the standard formula,
taken through a multiplication by six rather than a division, since the
printed division truncates over the integers.

## Falsifier

A modulus for which the fourfold sum differs from the cube of the modulus
times the sum of the first squares would contradict the theorem about the
defined sum.

## Evidence

- Module: `D5/S3/Factorization/A373561.lean`.
- Main theorem: `a373561`, stated for every natural modulus including zero.
- Layers: `gcd_buckets_eq_sum`, `triple_sum_eq`, `a373561_core`.
- The bucket collapse reuses `Finset.sum_fiberwise_of_maps_to`, already used
  in this repository by `D5/S3/Factorization/AlternatingGcdSumPillai`.
- There is no finite cutoff in any public statement.

The caller computed the sum by definition before dispatching an
implementation seat, and checked the reduction independently rather than
accepting it. The conjecture as printed held for every modulus through twelve
with no violation. The divisor of every summand landed inside the index range
for every modulus through fourteen, with no exception. The threefold sum with
the divisor layer removed matched the closed form for every modulus through
fifteen, and equalled the square of the modulus times the sum of squares over
the same range. At modulus six the summand vanished twice and was negative in
forty-eight of the triples, confirming that the zero and negative cases are
not vacuous.

## Triage

`theorem`. The identity is proved for every natural modulus. Nothing is
asserted about variants of the summand or about other members of the entry's
formula list.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The searches do not exclude
private or unindexed proofs. The identification with the OEIS entry is
documentary; the kernel verifies the explicitly defined sum.
