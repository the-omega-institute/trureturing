---
slug: oeis-a260310-balanced-prime-divisor-pair-mod-six-refutation
bibkey: wilson2015a260310
doi: null
url: https://oeis.org/A260310
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation
---

# Refutation of the A260310 balanced-pair mod-six conjecture

## Problem

OEIS A260310, NAME (verbatim):

> Pairs with balanced sums of prime divisors (A008472) and inverse prime divisors (A069359), ordered by larger members.

COMMENTS definition line (verbatim):

> Consider pairs (x,y) of numbers where sum(p|x) p + sum(q|y) q = x*sum(p|x) 1/p + y*sum(q|y) 1/q where p, q are primes and sum(p|x) p > sum(q|y) q.

COMMENTS conjecture line (verbatim; Robert G. Wilson v, Jul 22 2015):

> Conjecture: if a(2n-1) is prime then a(2n) is composite and vice versa. And when a(2n-1) is composite, it is congruent to 0 (mod 6). - _Robert G. Wilson v_, Jul 22 2015

AUTHOR line (verbatim):

> _Juri-Stepan Gerasimov_, Jul 22 2015

The first three pairs in the SEQUENCE lines are `(3, 8)`, `(7, 16)`, and
`(11, 18)`. The formal definitions use
`S(n) = ∑ p ∈ n.primeFactors, p` and the frozen repository definition
`squarefreeDeriv(n) = ∑ p ∈ n.primeFactors, n / p`, where the division is
natural-number division and is exact because each indexed prime divides `n`.
The predicate `IsPair(x, y)` means
`x < y ∧ S(x) + S(y) = squarefreeDeriv(x) + squarefreeDeriv(y) ∧ S(x) ≠ S(y) ∧ S(y) ≠ squarefreeDeriv(y)`.
The literal refuted clause is
`∀ x y : ℕ, IsPair x y → 1 < x → ¬ Nat.Prime x → 6 ∣ x`.

The prime/composite alternation sentence is not claimed. The separate remark
`a(2n) < a(2n+2)` is also not claimed; the 2015 b-file already refutes it at
`a(6552) = a(6554) = 35407`.

## Motivation

Wilson's 2015 comment makes a universal divisibility assertion about every
composite smaller member of a balanced pair. A kernel-checked balanced pair
whose composite smaller member is not divisible by six resolves that literal
clause without asserting either neighboring conjecture.

## Gap

Preregistration issue #7601 and its probe report record searches dated
September 14, 2026. All 32 OEIS revisions were read: revision #18 introduced
the conjecture, revision #20 changed punctuation, and Mathar's revisions #23
and #31 only explain why both members cannot be prime. Two metadata files in
OEIS Open arXiv:2608.11941v2 returned 0 references. Exact searches returned 0
results in formal-conjectures, LeanOpenProblems and LeanOpenProblems-results,
arXiv for `A260310`, `balanced sums of prime divisors`, and `xenial pairs`,
MathOverflow, and GitHub global search. OpenAlex returned HTTP 429 from its API
and HTTP 403 in the browser, so that surface is `ASSUMED-UNVERIFIED`. No proof
or refutation was found in the bounded surfaces that could be checked. This
does not assert exhaustive literature coverage or publication priority.

## Route

The module reuses the frozen definition
`D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv` directly. The
certificate factors `140140 = 2^2 * 5 * 7^2 * 11 * 13` and derives
`Nat.primeFactors 140140 = {2, 5, 7, 11, 13}` using
`Nat.primeFactors_mul`, `Nat.primeFactors_prime_pow`, and
`Nat.Prime.primeFactors`. It certifies `Nat.Prime 141601` and evaluates the
four sums. These facts establish `IsPair 140140 141601` and that 140140 is
composite, while `140140 % 6 = 4` contradicts the conjectured divisibility.

## Falsifier

A proof that every balanced pair with a composite smaller member greater than
one has that member divisible by six would falsify this refutation. The
kernel-checked pair `(140140, 141601)` satisfies the formal balanced-pair
predicate and proves `140140 % 6 = 4`, so such a proof would contradict the
formal result.

## Evidence

- Lean module:
  `D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- The profiled Lean process completed in 6.51 seconds, with cumulative kernel
  type-checking time 7.22 milliseconds and maximum resident set size
  2,919,399,424 bytes on an Apple M4 Pro with 64 GiB of memory.
- The formal `IsPair` definition directly consumes the frozen
  `D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv` owner rather
  than duplicating its body.
- The orchestrator independently obtained `S(140140) = 38`,
  `squarefreeDeriv(140140) = 141638`, `S(141601) = 141601`, and
  `squarefreeDeriv(141601) = 1`, so both sides equal 141639, while
  `140140 ≡ 4 (mod 6)`.
- The orchestrator scan for composite `c ≤ 300000`, with prime partner
  `q = squarefreeDeriv(c) - S(c) + 1`, found 26,235 pairs and exactly three
  composite-smaller members not divisible by six: `(140140, 141601)`,
  `(290290, 303337)`, and `(293930, 303049)`.
- The probe's independent sieve for `c ≤ 300000` found the same three among
  804 composite-smaller pairs. It also checked that the first three published
  pairs `(3, 8)`, `(7, 16)`, and `(11, 18)` satisfy `IsPair`.

The bounded computations beyond the displayed counterexample are supporting
evidence only. The formal result uses the single pair `(140140, 141601)`.

**Minimality (not claimed).**

The result does not assert that `(140140, 141601)` is the first counterexample
under the sequence's ordering or under any unbounded search. The two further
bounded examples show that the failure is not isolated, but the bounded scans
do not establish a global minimality theorem.

## Triage

`theorem`. The certified pair refutes the literal mod-six clause. It asserts
no result about the prime/composite alternation sentence, the monotonicity
remark, or any corrected form of the entry.

## ASSUMED-UNVERIFIED

OpenAlex was blocked by HTTP 429 and HTTP 403. The literature search is
bounded and does not establish exhaustive coverage or publication priority.
The bounded scans and any minimality reading are numerical evidence only; no
minimality theorem is formalized here.
