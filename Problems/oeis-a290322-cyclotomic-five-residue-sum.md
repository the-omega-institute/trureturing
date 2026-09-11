---
slug: oeis-a290322-cyclotomic-five-residue-sum
bibkey: oeis2024a290322
doi: null
url: https://oeis.org/A290322
triage: theorem
motivation_gids:
  - D5/S3/Arith/CyclotomicFiveResidueSum
---

# The A290322 admissible residue sum conjecture

## Problem

For a modulus at least two, call a residue below it admissible when it is
coprime to the modulus and the value of `u^4 + u^3 + u^2 + u + 1` at it is
coprime to the modulus as well. Robert Israel conjectured on January 23, 2024
that the sum of the admissible residues is not divisible by the modulus
whenever five divides the modulus.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection on September 9,
2026 found the statement still labelled Conjecture. The companion sequence
A290309 counts the same residues and is marked easy; the weighted first moment
is a different function and the counting results do not settle it.

## Gap

The searched public indexes returned no proof of this statement and no earlier
weighted-sum formula from which it follows. The polynomial-totient literature
reached through Csizmazia and Toth weights by a greatest common divisor rather
than by the residue, so its Euler products do not apply.

## Route

Write the modulus as a power of five times a factor prime to five, and let the
exponent of five be at least one.

The Chinese remainder theorem splits the admissible set as a product, and each
admissible residue of the five-part appears once for every admissible residue
of the other part. So the sum is congruent, modulo the power of five, to the
count on the prime-to-five part times the sum on the five-part.

Modulo five the cyclotomic value vanishes exactly at one, so the admissible
residues are exactly those congruent to two, three or four. Their
representatives modulo the power of five are those three residues shifted by
multiples of five, which gives a closed form for the sum by summing an
arithmetic progression. That closed form is congruent to the negative of the
next lower power of five.

For the remaining factor, over a prime field the product of the cyclotomic
value with one less than the variable is the fifth power minus one, and away
from characteristic five the value one is not a root, so the excluded units
are exactly the nontrivial fifth roots of unity. The unit group is cyclic, so
their number is the greatest common divisor of five with one less than the
prime. Either way the resulting count is prime to five, and multiplicativity
extends this to the whole factor.

Combining the three, the five-adic valuation of the sum is exactly one less
than that of the modulus, hence strictly smaller, so the modulus cannot divide
the sum.

## Falsifier

A modulus divisible by five whose admissible residues sum to a multiple of it
would contradict the theorem about the defined sum.

## Evidence

- Module: `D5/S3/Arith/CyclotomicFiveResidueSum.lean`.
- Main theorem: `residue_sum_ne_zero`.
- Supporting public results: `phi5_mod_five_eq_zero_iff`,
  `sum_goodUnits_five_pow`, `residue_sum_five_pow_ne_zero`, `residueCount_mul`,
  `sum_goodUnits_mul_cast`, `residueCount_pow`, `residueCount_prime`,
  `residueCount_not_dvd_five`.
- The module reuses `D5/S3/Arith/ChineseRemainder` rather than rebuilding the
  splitting.
- There is no finite cutoff in any public statement.

The caller computed the sums directly before dispatching an implementation
seat, and checked eight assertions rather than accepting the reduction it was
given. The conjecture itself held for all forty moduli divisible by five up to
two hundred, with no violation; for moduli not divisible by five the sum was a
multiple of the modulus in seventy-eight cases below one hundred and twenty,
which shows the divisibility hypothesis is doing real work rather than being
decorative. The cyclotomic value was congruent to zero modulo five exactly at
one. The admissible set for a power of five was exactly the residues congruent
to two, three or four, checked for the first three powers. The closed form for
the sum over a power of five was an exact equality for the first four powers,
and its congruence to the negative of the next lower power held for the first
six. The count formula for prime powers matched on thirteen primes for the
first two exponents with no mismatch, and no modulus prime to five below three
hundred had a count divisible by five.

## Triage

`theorem`. The conjecture is proved for every modulus divisible by five. The
module additionally records the exact five-adic valuation, which is stronger
than the nonvanishing that was asked for. Nothing is asserted about moduli not
divisible by five, where the sum frequently is a multiple of the modulus.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The searches do not exclude
private or unindexed proofs. The identification with the OEIS entry is
documentary; the kernel verifies the explicitly defined sum.
