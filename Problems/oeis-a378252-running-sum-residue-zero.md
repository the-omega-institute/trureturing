---
slug: oeis-a378252-running-sum-residue-zero
bibkey: oeis2025a378252
doi: null
url: https://oeis.org/A378252
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/RatajczakDoublingZero
---

# The A378252 running-sum residue conjecture

## Problem

Fix integers with the start value coprime to the modulus. Let the first term
be the start value reduced modulo the modulus, and each later term be the
start value plus every earlier term, again reduced. Lechoslaw Ratajczak
conjectured on October 13, 2025 that some term is zero exactly when the
modulus is a power of two, the exponent zero being allowed.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection on September 9,
2026 found the statement still labelled Conjecture, at revision 16 with no
later revision supplying a proof.

## Gap

The searched public indexes returned no proof, preprint or solution. The
obligation is an equivalence for all admissible pairs, not a finite check.

## Route

The recurrence appears to accumulate history but does not. Write the partial
sum as the start value plus the earlier terms. The next partial sum is the
previous one plus the previous term, and the previous term is the previous
partial sum reduced. Reducing before adding therefore turns the sum into
twice the previous term, so each term is the start value scaled by a power of
two and reduced.

Vanishing then says the modulus divides a power of two times the start value.
Coprimality moves the whole power onto the modulus, and a divisor of a power
of a prime is a power of that prime. Conversely, when the modulus is a power
of two, the term whose exponent matches is divisible by it.

## Falsifier

A coprime pair whose modulus is not a power of two yet whose sequence reaches
zero, or a power-of-two modulus whose sequence never does, would contradict
the theorem about the defined sequence.

## Evidence

- Module: `D5/S1/Recurrence/Parity/RatajczakDoublingZero.lean`.
- Theorems: `residue_eq_two_pow_mul`, `exists_zero_iff_modulus_pow_two`.
- The recurrence enters as a hypothesis on an arbitrary sequence, so no
  particular construction is privileged.
- There is no finite cutoff in either public statement.

The caller computed the sequence directly rather than accepting the seat's
reduction, and checked three separate readings. The closed form, that each
term is the start value scaled by a power of two and reduced, held for every
coprime pair with start value below 60 and every index through 40, with no
violation. The conjecture as printed, computing two hundred terms, held for
every coprime pair with start value below 200, with no violation. The reduced
divisibility form held for every coprime pair with start value below 300 and
exponents through 63, with no violation. The third reading is what the proof
establishes; the first is the bridge from the printed recurrence to it.

## Triage

`theorem`. The equivalence is proved for every coprime pair. Nothing is
asserted about the main A378252 sequence, which is a different object.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The searches do not exclude
private or unindexed proofs. The identification with the OEIS comment is
documentary; the kernel verifies the explicitly stated recurrence.
