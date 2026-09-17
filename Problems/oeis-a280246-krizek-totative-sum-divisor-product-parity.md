---
slug: oeis-a280246-krizek-totative-sum-divisor-product-parity
bibkey: krizek2016a280246
doi: null
url: https://oeis.org/A280246
triage: theorem
motivation_gids:
  - D5/S3/Arith/KrizekTotativeSumDivisorProductParity.result
---

# Totative-sum parity is preserved by the divisor product

## Problem

OEIS A280246 defines its sequence by the NAME line:

> a(n) = Product_{d|n} psi(d), where psi(m) is the sum of totatives of m (A023896).

Its COMMENT conjecture states:

> Conjecture: a(n) is odd iff the sum of totatives of n (A023896) is odd.

The sequence is attributed to Jaroslav Krizek, December 30, 2016; the
conjecture line has no separate author signature. The single assertion
anchored here is, for every natural n >= 1, that the product of the totative
sums over the positive divisors of n is odd if and only if the totative sum
of n is odd. No other A280246 comment is claimed.

## Motivation

A product is odd exactly when every factor is odd. The conjecture therefore
asks whether oddness of a totative sum propagates to every positive divisor
of its index.

## Gap

OEIS revision #10, September 10, 2025, retains the conjecture wording and
contains no bibliography or hyperlink proof entry. The protected-base
repository, pinned Mathlib, Loogle, and GitHub Lean searches supply no
totative-sum parity classification. These searches do not establish
exhaustive historical openness or priority.

## Route

For n > 1, pairing coprime residues k and n-k gives twice the totative sum
equal to n times its Euler totient. The prime-factor product formula then
excludes even n > 2, two distinct odd prime factors, and prime powers with
prime congruent to one modulo four. Consequently the odd totative sums
occur exactly at one, two, and positive powers of primes congruent to three
modulo four. This class is closed under positive divisors. The divisor
indexed by n supplies the converse implication for the product.

## Falsifier

A positive natural n whose divisor product and totative sum have different
parities would refute the assertion. The stated domain is unbounded; a
finite scan cannot settle it.

## Evidence

The definitions `totativeSum` and `divisorTotativeProduct` in
`D5/S3/Arith/KrizekTotativeSumDivisorProductParity.lean` are the literal
finite coprime sum and positive-divisor product. Its theorem
`odd_totativeSum_iff` supplies the prime-power classification, and `result`
proves the parity equivalence for every natural n satisfying 1 <= n.

## Triage

`theorem`. The A280246 parity conjecture is proved on its positive-natural
domain. The Scribe claim binds this assertion to `result` with kind `proved`.

## ASSUMED-UNVERIFIED

Historical openness and priority beyond the checked OEIS record,
repository, pinned Mathlib, Loogle, and GitHub Lean surfaces are unverified.
The resolution registration does not itself machine-prove fidelity to the
natural-language source; the explicit positive-domain statement fixes that
semantic boundary.
