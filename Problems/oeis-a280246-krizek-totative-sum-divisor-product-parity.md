---
slug: oeis-a280246-krizek-totative-sum-divisor-product-parity
bibkey: krizek2016a280246
doi: null
url: https://oeis.org/A280246
triage: theorem
motivation_gids:
  - D5/S3/Arith/KrizekTotativeSumDivisorProductParity.result
---

# OEIS A280246 totative-sum divisor-product parity

## Problem

OEIS A280246, NAME (`%N`, verbatim):

> a(n) = Product_{d|n} psi(d), where psi(m) is the sum of totatives of m (A023896).

COMMENT (`%C`, verbatim):

> Conjecture: a(n) is odd iff the sum of totatives of n (A023896) is odd.

AUTHOR (`%A`, verbatim):

> _Jaroslav Krizek_, Dec 30 2016

The comment does not separately name its author. The sequence starts at one.
For every natural number `n >= 1`, let `psi(n)` be the sum of the natural
numbers from one through `n` that are coprime to `n`. The conjecture states
that the product of `psi(d)` over all positive divisors `d` of `n` is odd if
and only if `psi(n)` is odd.

## Motivation

The parity equivalence identifies oddness of a divisor product with a
property of its factor at the full index. The frozen declaration named above
proves this equivalence for every positive natural number, not a finite
initial segment.

## Gap

The checked OEIS record labels the parity equivalence as a conjecture and
contains no bibliography or hyperlink entry to a proof. The preregistered
classification on issue #8390 supplies its arithmetic content: odd totative
sums occur exactly at one, two, and positive powers of primes congruent to
three modulo four. The searched repository and pinned-library scope contains
no dominating theorem for that classification or the conjecture.

## Route

For `n > 1`, the involution `k -> n-k` on reduced residues proves
`2*psi(n) = n*phi(n)`. Oddness excludes even indices above two and indices
with two distinct odd prime factors. A prime power survives exactly when its
prime is congruent to three modulo four. Every positive divisor of an index
in this classification is again in the classification. A finite natural
product is odd exactly when every factor is odd, and the divisor indexed by
`n` gives the converse direction.

## Falsifier

A positive natural number for which the divisor product and its totative sum
have different parity would refute the conjecture. Agreement on any finite
initial segment does not establish the universal statement.

## Evidence

- Source: https://oeis.org/A280246, revision #10, September 10, 2025.
- Preregistration: https://github.com/the-omega-institute/trureturing/issues/8390.
- Formal module: `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.lean`.
- `totativeSum` is the literal finite coprime sum; including zero contributes
  zero and does not change the sum over one through `n`.
- `divisorTotativeProduct` is the product over the positive-divisor finset.
- `two_mul_totativeSum` proves the pairing identity.
- `odd_totativeSum_iff` proves the complete odd-sum classification.
- `result` proves the quoted parity equivalence for every `n >= 1`.
- The three theorem axiom closures are `[propext, Classical.choice, Quot.sound]`.

## Triage

`theorem`; the universal positive-index parity equivalence is proved by
`D5/S3/Arith/KrizekTotativeSumDivisorProductParity.result`.

## ASSUMED-UNVERIFIED

Historical openness and priority beyond the checked OEIS record, issue
#8390, repository, pinned Mathlib, Loogle, and GitHub Lean-code searches are
unverified. No exhaustive literature-wide novelty claim is made. The
resolution annotation records the repository's statement-to-problem mapping;
the kernel verifies the Lean theorem, not the natural-language mapping.
