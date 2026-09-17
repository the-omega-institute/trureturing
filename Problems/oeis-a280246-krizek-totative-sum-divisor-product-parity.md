---
slug: oeis-a280246-krizek-totative-sum-divisor-product-parity
bibkey: krizek2016a280246
doi: null
url: https://oeis.org/A280246
triage: theorem
motivation_gids:
  - D5/S3/Arith/KrizekTotativeSumDivisorProductParity.result
---

# Krizek's A280246 totative-sum divisor-product parity conjecture

## Problem

OEIS A280246 defines

> a(n) = Product_{d|n} psi(d), where psi(m) is the sum of totatives of m (A023896).

Its conjecture line states

> Conjecture: a(n) is odd iff the sum of totatives of n (A023896) is odd.

The proved statement quantifies over every natural `n` satisfying `1 <= n`.
It defines `psi(n)` as the sum of the natural numbers from zero through `n`
that are coprime to `n`, and defines `a(n)` as the product of `psi(d)` over
the positive divisors `d` of `n`.

## Motivation

The conjecture asks for a uniform parity characterization of a divisor-indexed
product rather than a bounded computation. Issue #8390 registered the exact
positive-natural statement and the proposed totative-sum classification before
the proof was constructed.

## Gap

OEIS revision 10, dated 2025-09-10, still labels the assertion as a
`Conjecture`. The entry contains no `%D` references and no `%H` links, and its
formula line restates only the defining divisor product. Searches of pinned
Mathlib, the repository, Loogle, GitHub Lean code, and the OEIS entry found no
proof or refutation of this parity characterization.

The repository searches found no prior `A280246`, `A023896`, totative-sum
carrier, target declaration name, or matching conclusion shape. The nearby
totient-parity results concern the distinct Lehmer condition
`totient(n) | n-1` and do not imply this classification.

## Route

1. Pair each reduced residue `k` modulo `n` with `n-k` to obtain
   `2 * psi(n) = n * totient(n)` for `n > 1`.
2. Classify odd `psi(n)`: besides `n=1` and `n=2`, exactly the positive powers
   of primes congruent to three modulo four occur.
3. Show that this classification is closed under taking positive divisors.
4. Use that a finite natural product is odd exactly when every factor is odd;
   the factor indexed by `n` gives the reverse implication.

## Falsifier

Any positive natural `n` for which the divisor product of totative sums and
the totative sum of `n` have different parity would falsify the theorem. A
failure of the intermediate classification at any natural `n` would also
invalidate the forward divisor-closure argument.

## Evidence

- Lean module:
  `D5/S3/Arith/KrizekTotativeSumDivisorProductParity.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- The classification theorem `odd_totativeSum_iff` is on the live dependency
  path to both directions of `result`; deleting it makes the module fail at
  both use sites.
- Exact integer checks found no conjecture failures for `1 <= n <= 5000` and
  no classification disagreements for `1 <= n <= 20000`.
- The source definitions and all theorem clauses are represented in the
  emitted Blueprint formulas, including the positive guard on `result`.

## Triage

`theorem`; resolution `proved` for the positive-natural A280246 parity
conjecture. The result is universal and symbolic, not a finite-instance
certificate.

## ASSUMED-UNVERIFIED

The bounded checks do not establish the universal statement. Historical
openness beyond the OEIS record and the searched repository, pinned Mathlib,
Loogle, and GitHub Lean-code surfaces is unverified; no exhaustive global
novelty or priority claim is made.
