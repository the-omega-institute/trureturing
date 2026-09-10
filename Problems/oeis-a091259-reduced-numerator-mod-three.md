---
slug: oeis-a091259-reduced-numerator-mod-three
bibkey: oeis2024a091259
doi: null
url: https://oeis.org/A091259
triage: theorem
motivation_gids:
  - D5/S3/Factorization/A091259
---

# The A091259 congruence

## Problem

Take the ratio of the divisor sum of cubes to the ordinary divisor sum, reduce
it to lowest terms, and read the numerator modulo three. Michel Marcus
conjectured on August 11, 2024 that the result is the indicator of a
prime-exponent condition: one exactly when every prime congruent to two modulo
three occurs to an even exponent, zero otherwise.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection on September 9,
2026 found it still labelled Conjecture, and the entry is marked easy.

## Gap

The prime-exponent criterion is printed on the neighbouring entry, so the
statement can be posed without reproving the classical equivalence behind it.
What neither entry supplies is the effect of the reduction: cancelling the
fraction could consume a factor of three or leave one behind. The searched
indexes returned no proof.

## Route

At a prime power the ratio of the two divisor sums equals a ratio of values of
the quadratic whose roots are the primitive cube roots of unity, with the
argument raised one exponent higher in the numerator. In that form the
residues are immediate: a prime congruent to two contributes zero at odd
exponents and one at even ones; the prime three contributes one on both sides;
a prime congruent to one contributes a single factor of three on each side,
and the quotients are one modulo three.

The reduction is handled without tracking exponents. If a cross-multiplication
relates two pairs and every divisor of the denominator side is one modulo
three, then the reduced numerator agrees modulo three with the other
numerator. Applied with the denominator side built from the local factors with
their threes stripped, this gives the result whatever the cancellation
happened to remove.

The adjacent conjecture about which denominators occur is not needed; only its
easy direction, that every prime factor of the reduced denominator is one
modulo three, and that direction is what the stripped construction supplies.

## Falsifier

A positive argument whose reduced numerator modulo three differs from the
indicator would contradict the theorem about the defined quantities.

## Evidence

- Module: `D5/S3/Factorization/A091259.lean`.
- Main theorem: `a091259_mod_three`, for every positive argument.
- The general reduction lemma is `reduced_numerator_mod_three`; the local
  classification is `localNumerator_mod`; the assembly is
  `localNumerator_prod_mod`.
- Supporting results include the prime-power ratio identity, the behaviour of
  the quadratic modulo three, and the stripped-three construction with its
  divisor property.
- All public results are within the standard three axioms with no `sorryAx`.
- There is no finite cutoff in the public statement.

The caller verified before dispatching an implementation seat. The congruence
held for every argument through three thousand with no violation. The
numerator modulo three took only the two values the indicator can take, never
the third. The prime-power ratio identity matched for eleven primes at
exponents one through six with no mismatch. The four residue cases were
checked individually, including that a prime congruent to one leaves a
quotient of one modulo three after removing its single factor of three.

## Triage

`theorem`. The congruence is proved for every positive argument. The classical
equivalence behind the indicator is not reproved, and the adjacent conjecture
about the set of denominators is untouched.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The searches do not exclude
private or unindexed proofs. The identification with the two OEIS entries is
documentary; the kernel verifies the explicitly defined quantities. The seat
reported an independent recomputation to twenty thousand; the caller checked
to three thousand only.
