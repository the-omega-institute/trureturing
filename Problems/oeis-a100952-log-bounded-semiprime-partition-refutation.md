---
slug: oeis-a100952-log-bounded-semiprime-partition-refutation
bibkey: vospost2004a100952
doi: null
url: https://oeis.org/A100952
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation
---

# Refutation of the A100952 log-bounded semiprime-partition conjecture

## Problem

OEIS A100952, NAME (verbatim):

> Numbers that cannot be written as p*q+r with three distinct primes p, q and r.

COMMENT (verbatim; Jonathan Vos Post, Nov 25 2004):

> A weaker conjecture: every integer greater than 60 (or some larger value based on further search) may be partitioned into a prime p and a semiprime qr, where the prime p is bounded by log(min(q,r)). Chen (1978) showed that all sufficiently large even numbers are the sum of a prime and the product of at most two primes. Zumkeller's conjecture effectively extends this from "even" to both even and odd integers. - _Jonathan Vos Post_, Nov 25 2004

AUTHOR (verbatim):

> _Reinhard Zumkeller_, Nov 23 2004

The literal refuted statement is
`exists B : Nat, 60 <= B and forall m : Nat, B < m -> Rep m`, where
`Rep m` means that there exist natural primes `p`, `q`, and `r` satisfying
`m = p + q*r` and
`(p : Real) <= Real.log ((min q r : Nat) : Real)`. Here `Real.log` is the
natural logarithm, equal factors `q = r` are allowed, and no distinctness
condition is imposed. The refutation therefore covers every stricter reading
that requires the three primes to be distinct. It does not resolve the
completeness conjecture for A100952 or Seidov's `p*q-r` conjecture.

## Motivation

The OEIS comment asks for one threshold after which every integer has a
log-bounded prime-plus-semiprime representation. A symbolic obstruction for
the entire residue class five modulo six disproves every possible threshold,
including thresholds larger than sixty.

## Gap

Preregistration issue #7620 and its probe report record searches dated
September 14, 2026. The OEIS aggregate history records a 2015 edit from `ln`
to `log` and contains no proof or refutation. Individual early revision pages
returned HTTP 403 and are `ASSUMED-UNVERIFIED`. An exact arXiv search returned
0 results. OpenAlex autocomplete returned 0 results, its `/works` endpoint
returned HTTP 429, and its web page returned HTTP 403; the latter two surfaces
are `ASSUMED-UNVERIFIED`. Crossref returned 0 results, MathOverflow returned 0
results, and a GitHub exact-phrase search returned 0 results.

PlanetMath material about Chen's theorem and Zumkeller's conjecture supplies
background but does not dominate the logarithmic bound. An external AI
discussion dated May 9, 2026 had a redirecting full-text link and is
`ASSUMED-UNVERIFIED`; its abstract concerns only finiteness. Chen's 1978
theorem has no logarithmic bound and does not cover odd integers. These are
bounded search surfaces, not an exhaustive literature result, and no priority
claim is made.

## Route

For `m = 6*t+5`, suppose a representation exists.

1. If `min(q,r) <= 3`, then primality gives `2 <= p`, while
   `Real.log_lt_sub_one_of_pos` gives `log(min(q,r)) < min(q,r)-1 <= 2`,
   contradicting the logarithmic bound. Hence `q > 3` and `r > 3`.
2. The primes `q` and `r` are odd. Since `m` is odd and `q*r` is odd, parity
   forces the prime `p` to equal two.
3. The equation becomes `q*r = 6*t+3 = 3*(2*t+1)`. Euclid's lemma for primes
   forces `q = 3` or `r = 3`, contradicting the first step.
4. Given any proposed threshold `B`, the value `m = 6*(B+10)+5` is above `B`
   and belongs to the forbidden residue class, so the eventual claim fails.

## Falsifier

The refutation would fail if `Real.log_lt_sub_one_of_pos` did not yield the
strict bound used for `min(q,r)` in the range from two through three, if a
prime above three could be even, if primality did not convert divisibility by
three into equality with three, or if `6*(B+10)+5` were not above every
proposed natural threshold `B`.

## Evidence

- Lean module:
  `D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.lean`.
- Main theorem: `result : not claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- On the stamped hot tree, the kernel run took 11.53 seconds wall time,
  reported 52.8 milliseconds of cumulative type checking, and used
  2,156,838,912 bytes maximum resident set size.
- The orchestrator checked the 3,323 integers `m` with `61 <= m <= 20000` and
  `m` congruent to five modulo six; 0 were representable.
- On `(60, 2000]`, the orchestrator found 197 representable integers; the
  first eight were 123, 145, 171, 189, 211, 223, 249, and 255.
- The search seat checked all 499,970 odd integers with
  `61 <= m <= 10^6`; 108,602 were representable, while all 166,656 values
  congruent to five modulo six failed.
- The probe repeated the range through 20,000 and obtained the same readings.

The bounded searches are observations and do not carry the theorem. The Lean
proof establishes the infinite residue-class obstruction symbolically.

## Triage

`theorem`. The formal result refutes the log-bounded sub-conjecture by proving
that no threshold works. It makes no claim about the completeness of A100952,
Seidov's conjecture, or priority.

The module is classified `utility: none`. The declarations `Rep` and `claim`
are definitions. The theorem `result` is a symbolic refutation by an infinite
family using a real-log estimate and residue classification; none of
`bounded-enumeration`, `checker`, `numeric-reduction`, or
`certified-instance` applies. The open-problem resolution kind is `Refuted`.

## ASSUMED-UNVERIFIED

The individual early OEIS revision pages, the OpenAlex `/works` endpoint and
web page, and the full text of the external May 9, 2026 discussion were not
retrieved for the reasons recorded above. The orchestrator, search-seat, and
probe bounded-search readings were supplied by issue #7620 and were not
recomputed by this implementation seat. No arXiv-complete, OpenAlex-complete,
or priority claim is made.
