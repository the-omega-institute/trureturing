---
slug: oeis-a227244-c2-equality
bibkey: wu2026a227244
doi: null
url: https://oeis.org/A227244/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/WuA227244C2Equality.result
---

# A227244 Conjecture 2: exact least prime divisor

## Problem

Chai Wah Wu's FORMULA line in OEIS A227244, revision 54:

> Conjecture 2: a(220*n+8) = 47 for n >= 0.

Here a(m) is the smallest prime factor of
`G(m) = ((2 : Int)^(2^m)+1)*(2 : Int)^(2^(2^m))-1`.
Every exponent is natural; multiplication and subtraction are signed integer operations.
The complete assertion is `forall n : Nat, 47.Prime and (47 : Int) | G(220*n+8) and forall q : Nat, q.Prime -> (q : Int) | G(220*n+8) -> 47 <= q`.
There is no exclusion, finite cutoff or positivity restriction on n.

## Motivation

The equality identifies the least prime factor throughout an infinite arithmetic
progression. Divisibility by 47 alone does not exclude smaller prime factors.
The adjacent 2026 Conjecture 1 concerns `a(20*n+16) = 101`, stronger than the
COMMENT bound `a(20*n+16) <= 101`. The 2019 first-conjecture proof concerns the
older `a(n) >= 11` statement. Neither settles this Conjecture 2 equality; the
entry's adjacent conjectures are separate assertions.

## Gap

The exact equality requires primality of 47, divisibility of every
`G(220*n+8)` by 47, and exclusion of every smaller natural prime divisor.
The canonical result supplies all three clauses for every natural n, including
zero. Thus the gap between divisibility and the exact least prime factor is
closed for this progression; no claim about other progressions follows here.

## Route

Periodic exponent reduction gives a finite modular certificate for divisibility
by 47. The same reduction excludes each smaller prime. Primality of 47, its
divisibility, and the lower bound for every prime divisor together give the exact
smallest-prime-factor equality for every natural n.

## Falsifier

A natural n for which 47 does not divide `G(220*n+8)`, or a natural prime
`q < 47` dividing that integer, would contradict the equality. The case `n = 0`
is included. A finite sample without such a counterexample would not establish
the universal statement; the periodic reductions cover all natural n.

## Evidence

The canonical theorem is `D5.S3.Arith.Congruence.WuA227244C2Equality.result`.
It states primality, signed integer divisibility and the lower bound on every
natural prime divisor specified in Problem. Its modular periodicity and cast
APIs are reused directly; the finite residue tables discharge universal
reductions rather than replace the theorem by a finite instance.

The source is Chai Wah Wu's 2026 Conjecture 2 in OEIS A227244, revision 54,
identified by `wu2026a227244` and the official URL in the frontmatter.
The primary internal and text surfaces retain the quoted conjecture.
Bounded local/private, pinned Mathlib, third-party and arXiv identifier searches
found no exact resolved supplier on the checked surfaces. No corresponding
theory volume was identified by the A227244 and progression searches.

## Triage

`theorem`: the canonical result establishes the exact unbounded equality.
The result and every retained private helper have `proof_shape: bind-only` and
`escape_witness: none`. The result's sole admission basis is
`open-problem-resolution`; the private helpers have live consumers in its proof
dependency closure. The result has `utility: none`. This is an external
open-problem resolution, with no new general method or additional mathematical
result claimed by this dossier.

## ASSUMED-UNVERIFIED

The four-slot escape audit remains unfinished in
[issue #27402, comment 6694571880](https://github.com/the-omega-institute/trureturing/issues/27402#issuecomment-6694571880);
it is not `declared_validated`. The bounded source searches do not establish
global semantic absence of an earlier resolution or historical priority.
This dossier does not certify frozen membership or publication.
