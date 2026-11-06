---
slug: oeis-a227244-c1-equality
bibkey: wu2026a227244
doi: null
url: https://oeis.org/A227244/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/WuA227244C1Equality.result
---

# A227244 Conjecture 1: exact least prime divisor

## Problem

Chai Wah Wu's FORMULA line in OEIS A227244, revision 54:

> Conjecture 1: a(20*n+16) = 101 for n >= 0.

Here a(m) is the smallest prime factor of
`G(m) = ((2 : Int)^(2^m)+1)*(2 : Int)^(2^(2^m))-1`.
Every exponent is natural; multiplication and subtraction are signed integer operations.
The complete assertion is `forall n : Nat, 101.Prime and (101 : Int) | G(20*n+16) and forall q : Nat, q.Prime -> (q : Int) | G(20*n+16) -> 101 <= q`.
There is no exclusion, finite cutoff or positivity restriction on n.

## Source boundary

The 2026 Conjecture 1 equality is stronger than the COMMENT theorem giving
only `a(20*n+16) <= 101`. The 2019 first-conjecture proof concerns the older
`a(n) >= 11` statement. Neither substitutes for the present equality.
The entry's adjacent conjectures are separate assertions.

## Provenance and scope

The accepted solution is identified by issue #27408 and the completed submission
SHA256 `e8fc1901c0f31335d9e1d311c071c87074258e9730df18c35b13b8b80edb5fad`. Its modular periodicity and cast APIs are reused directly.
The canonical result and every retained private helper have `proof_shape: bind-only`;
`escape_witness: none`; the result's sole admission basis is
`open-problem-resolution`. Private helpers have live consumers in the result's
proof dependency closure. No general method or historical priority is asserted.

The bounded source qualification and local/private/pinned Mathlib/third-party/arXiv
identifier searches supplied with the accepted solution found no exact resolved
supplier on those checked surfaces. This is no assertion of global semantic
absence. The primary internal and text surfaces retain the quoted conjecture.
No corresponding theory volume was found by the A227244 and progression searches.
The unbounded result has `utility: none`: finite modular tables discharge universal
periodicity reductions rather than replace the statement by a finite instance.

## Route

Periodic exponent reduction gives a finite modular certificate for divisibility
by 101. The same reduction excludes each smaller prime. Primality of 101, its
divisibility, and the lower bound for every prime divisor together give the exact
smallest-prime-factor equality for every natural n.

## Evidence boundary

The canonical theorem is `D5.S3.Arith.Congruence.WuA227244C1Equality.result`.
Current kernel, axiom, rendered-statement and audit evidence must concern this
canonical source; acceptance of the original bytes alone does not certify it.
No frozen membership or publication is asserted here.
