---
slug: oeis-a136162-krizek-next-prime-product-quadruplet
bibkey: smith2017a136162
doi: null
url: https://oeis.org/A136162
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet
---

# The A136162 next-prime product has four prime neighbors only at q=3

## Problem

OEIS A136162, NAME (`%N`, verbatim):

> List of prime quadruplets {p, p+2, p+6, p+8}.

Jaroslav Krizek's COMMENT (`%C`, verbatim, including both sentences and its
attribution):

> {11, 13, 17, 19} is the only prime quadruplet {p, p+2, p+6, p+8} of the form {Q-4, Q-2, Q+2, Q+4} where Q is a product of a pair of twin primes {q, q+2} (for prime q = 3) because numbers Q-2 and Q+4 are for q>3 composites of the form 3*(12*k^2-1) and 3*(12*k^2+1) respectively (k is an integer). Conjecture: {11, 13, 17, 19} is the only prime quadruplet {p, p+2, p+6, p+8} of the form {q*(nextprime(q))-4, q*( nextprime(q))-2, q*( nextprime(q))+2, q*( nextprime(q))+4} where q is a prime (for prime q = 3). - _Jaroslav Krizek_, Jul 07 2017

Define `nextPrime(q)` as the least prime greater than or equal to `q+1`,
implemented by `Nat.find (Nat.exists_infinite_primes (q + 1))`, and define
`Q(q) = q * nextPrime(q)`. The literal proved statement is
`forall q : Nat, q.Prime -> ((Nat.Prime (Q q - 4) and
Nat.Prime (Q q - 2) and Nat.Prime (Q q + 2) and Nat.Prime (Q q + 4)) iff
q = 3)`.

The preceding twin-prime-product sentence, any other property or
classification of prime quadruplets, and every other A136162 comment are NOT
claimed. Natural subtraction is truncated subtraction.

## Motivation

Krizek's comment asks whether multiplying a prime by its successor prime can
place all four offsets two and four on primes only in the displayed
quadruplet. The theorem resolves that universal characterization for every
prime input.

## Gap

On 2026-09-15, all 25 revisions of OEIS A136162 were read. The conjecture was
added in revision #7 on 2017-07-09 and was still present in the latest comment
revision, #22 on 2019-03-29; revisions #23 through #25 changed only status or
links. The arXiv API returned zero results, OpenAlex returned zero results,
and MathOverflow returned zero results for the checked A136162/conjecture
queries. GitHub identifier searches returned two Java sequence generators,
not proofs or refutations.

These checked surfaces do not establish exhaustive literature coverage, and
no priority claim is made.

## Route

1. The prime input `q=2` gives `Q-2=4`, so the four primality assumptions
   fail; `q=3` gives `Q=15` and the prime neighbors `11, 13, 17, 19`.
2. For prime `q>=5`, both `q` and `nextPrime(q)` are nonzero modulo three.
3. Their product `Q` is therefore congruent to one or two modulo three. In
   the first case `Q+2` is divisible by three; in the second, `Q-2` is.
4. The selected neighbor exceeds three, contradicting its asserted
   primality. Thus the conjunction forces `q=3`, and the explicit small case
   proves the converse.

## Falsifier

Any prime natural `q` other than three for which `Q(q)-4`, `Q(q)-2`,
`Q(q)+2`, and `Q(q)+4` are all prime would contradict the theorem. Failure of
primality for any of `11`, `13`, `17`, or `19` would contradict its converse.
The kernel-checked result quantifies over every prime natural `q`.

## Evidence

- Lean module:
  `D5/S3/Arith/Congruence/KrizekNextPrimeProductQuadruplet.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 6.98 seconds, type checking
  87 milliseconds, and maximum resident set size 1,451,982,848 bytes.
- Deleting any one of the three direct Mathlib imports makes the module fail
  to compile; restoring all three gives a zero-exit single-file profile
  build.
- The probe scanned all 17,984 primes `q < 200000` and found only `q=3`.
- The bounded scan supports fault detection only; the modulo-three split and
  the two small cases carry the universal proof.

## Triage

`theorem`. Krizek's next-prime-product characterization is proved for every
prime natural `q`; the resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

The bounded scan does not establish the universal statement. Historical
openness outside the checked OEIS history, arXiv, OpenAlex, MathOverflow, and
GitHub surfaces is unverified; no exhaustive literature or priority claim is
made.
