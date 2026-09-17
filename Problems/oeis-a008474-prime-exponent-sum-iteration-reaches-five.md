---
slug: oeis-a008474-prime-exponent-sum-iteration-reaches-five
bibkey: ianakiev2014a008474
doi: null
url: https://oeis.org/A008474
triage: theorem
motivation_gids:
  - D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive
---

# The A008474 prime-exponent sum iteration reaches five

## Problem

OEIS A008474, NAME (`%N`, verbatim):

> If n = Product (p_j^k_j) then a(n) = Sum (p_j + k_j).

COMMENT (`%C`, verbatim):

> Conjecture: for m > 4, by iterating the map m -> A008474(m) one always reaches 5 [tested up to m = 320000]. - _Ivan N. Ianakiev_, Nov 10 2014

FORMULA (`%F`, verbatim):

> Additive with a(p^e) = p + e.

AUTHOR (`%A`, verbatim):

> _Olivier Gérard_

The first terms (`%S`, verbatim excerpt) are
`0,3,4,4,6,7,8,5,5,9,12,8,14,...`.

For every natural n, define
`F(n) = Sum (p + factorization(n)(p))` over `p` in `primeFactors(n)`. The
literal proved statement is
`forall m : Nat, 4 < m -> exists t : Nat, F^[t](m) = 5`. Thus "reaches 5"
means that some finite iterate equals 5. The values follow the cycle
`5 -> 6 -> 7 -> 8 -> 5`; four is a fixed point, so `m > 4` is sharp; and
`2 -> 3 -> 4` never reaches five. The generating function and the identities
with A001222 and A008472 are NOT claimed.

## Motivation

The conjecture asks for a global termination statement about an arithmetic
map defined from the complete prime factorization of its input. The proof
turns the orbit question into strict descent while preserving the lower bound
five.

## Gap

The dated surfaces recorded in preregistration issue #7647 and the probe were
all 64 revisions of OEIS A008474. The conjecture is unchanged in revision #64
of 2025-12-23, which added Krueger's formula. Daniel Tsai, Integers 21 (2021),
Article #A32, was read in full: its v-function omits exponent one and the paper
does not study this iteration. Searches returned arXiv 0, MathOverflow 0,
Crossref 0, and GitHub 0. OpenAlex returned HTTP 429 - ASSUMED-UNVERIFIED.
No priority claim is made.

## Route

(a) Establish coprime additivity of F and the value `F(p^e) = p + e` for prime
p and positive e. (b) Prove `F(n) <= n + 1` for every `n >= 2`. (c) Prove
`F(n) >= 5` for `n >= 5`, and one-step descent `F(n) < n` for composite
`n > 4` other than six. (d) Prove `F(2n) <= F(n) + 3` and the prime two-step
descent `F(F(p)) < p` for primes `p >= 11`. (e) Verify the four-cycle and close
the theorem by strong induction.

## Falsifier

A natural m greater than four whose every finite F-iterate differs from five
would refute the theorem.

## Evidence

- Lean module: `D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive.lean`.
- Main theorem: `ianakiev_a008474`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile after normalization inlining and import minimization: 9.85 s
  wall time, 266 ms cumulative type checking, and 1706754048 bytes maximum RSS.
- Orchestrator check: every `5 <= m <= 10^5` reaches five, with maximum first
  hitting time 13 at `m = 26833`.
- Probe check: every `5 <= m <= 10^6` reaches five, with maximum first hitting
  time 15 at `m = 461938`.
- Search-seat check: the same range through `10^6`, maximum 15 steps at
  `m = 461938`.
- The proof asserts no generating-function formula, no A001222 or A008472
  identity, and no theorem about Tsai's v-palindromes.

## Triage

`theorem`

## ASSUMED-UNVERIFIED

The OpenAlex search was rate-limited, the bounded orbit searches are finite,
and no priority claim is made. The literature search is not an exhaustive
proof of novelty.
