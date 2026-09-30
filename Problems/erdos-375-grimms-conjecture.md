---
slug: erdos-375-grimms-conjecture
bibkey: erdos1971grimm
doi: null
url: https://www.erdosproblems.com/375
triage: wall
motivation_gids:
  - D5/S3/PrimeGaps/GreedyResidues
---

# Erdős #375: Grimm's conjecture

## Problem

The [Erdős Problems entry](https://www.erdosproblems.com/375) asks whether,
for every `n, k >= 1`, if `n + 1, ..., n + k` are all composite, there are
distinct primes `p_1, ..., p_k` with `p_i | n + i`. The page was checked on
30 September 2026: it is marked **FALSIFIABLE / open**, and lists zero proof
claims. It records substantial finite verification and asymptotic ranges, but
also explicitly says that computation is not a proof and the conjecture
remains open.

This repository contribution proves the first nontrivial bounded case. For
three consecutive composite terms beginning at `n + 1`, it constructs three
pairwise distinct prime divisors. The formal theorem is
`D5.S3.Arith.Congruence.Erdos375ThreeComposites.exists_distinct_prime_divisors_of_three_composites`.

## Motivation

The proof uses the elementary fact that consecutive integers are coprime. For
the two endpoints, either an odd prime divisor exists or the endpoint is
divisible by four. Both endpoints cannot be divisible by four because their
difference is two. An odd endpoint prime cannot divide the other endpoint for
the same difference reason; the middle prime is separated from both by
coprimality.

This is the first case beyond the page's stated trivial range `k <= 2`. It
tests the distinct-representative mechanism in a form small enough for a
fully checked proof while retaining the arithmetic obstruction used by the
unrestricted question.

## Gap

The unrestricted matching problem for an arbitrary run of composite integers
is not supplied by this three-term theorem. In particular, no uniform result
for `k >= 4` follows from it.

## Route

The formal route is the D5 module named above, using only pinned Mathlib
prime-divisor, coprimality, and natural-number divisibility lemmas.

## Falsifier

A counterexample to the formal target would be a positive `n` with the three
terms composite but no three pairwise distinct prime divisors assigned to the
corresponding terms. Such an `n` would contradict the compiled Lean theorem.

## Evidence

The source page was checked on 30 September 2026 and is marked
FALSIFIABLE/open with zero proof claims. It records finite verification and
known asymptotic ranges, while explicitly saying that computation is not a
proof. The repository search at the base commit found no existing #375 module.

## Triage

This is a wall candidate for the named open problem: the bounded theorem is
proved, while the full conjecture remains open. No priority claim is made;
the source page and cited literature are documentary evidence, while the Lean
kernel is the authority for the bounded theorem.

## ASSUMED-UNVERIFIED

The web-page status and scoped repository search are source checks rather than
a worldwide priority certificate. The residual `k >= 4` problem is not
claimed solved by this contribution.

- [Erdős Problems #375](https://www.erdosproblems.com/375), accessed 30
  September 2026: exact statement, open status, zero proof claims, and the
  reported finite and asymptotic ranges.
- [Laishram--Shorey, Grimm's conjecture on consecutive integers (2006)](https://www.isid.ac.in/~shanta/PAPERS/Grimm-IJNT.pdf): a cited finite range,
  retained here only as context and not imported as a formal premise.
- [Erdős--Selfridge (1971)](https://users.renyi.hu/~p_erdos/1971-24.pdf):
  cited historical context for the conjecture's consequences.
