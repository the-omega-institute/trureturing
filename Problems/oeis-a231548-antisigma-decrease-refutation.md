---
slug: oeis-a231548-antisigma-decrease-refutation
bibkey: krizek2013a231548
doi: null
url: https://oeis.org/A231548
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation
---

# Refutation of the A231548 antisigma gap-three conjecture

## Problem

OEIS A231548, NAME (verbatim):

> Numbers n such that 2*n - 1 < sigma(n) - sigma(n-2).

COMMENT defining antisigma (verbatim):

> Also numbers n such that antisigma(n) < antisigma(n-2), where antisigma(n) = A024816(n) = the sum of the non-divisors of n that are between 1 and n.

COMMENT conjecture line (verbatim; Jaroslav Krizek, Nov 12 2013):

> Conjecture: there are no numbers n such that antisigma(n) < antisigma(n-3). - _Jaroslav Krizek_, Nov 12 2013

OEIS A024816, NAME (verbatim):

> Antisigma(n): Sum of the numbers less than n that do not divide n.

The literal object is
`antisigma(n) = Σ of d ∈ [1,n] with d ∤ n`. Since `n`
always divides itself, this agrees with the A024816 interval ending before
`n`. The conjecture is the claim
`∀ n ≥ 3, antisigma(n-3) ≤ antisigma(n)`.

## Motivation

This first-tier OEIS conjecture was printed in 2013 and remains a universal
claim about the behavior of the antisigma function. A certified
counterexample resolves the literal conjecture without proposing a corrected
statement.

## Gap

Preregistration issue #7485 and its probe report record searches dated
September 13, 2026. OEIS history revisions #1 through #13 only introduce and
reword the conjecture: revision #2 says "not numbers", revision #10 changes
that phrase to "no numbers", and revision #13 retains the current wording.
No proof or refutation appears in those revisions. Exact searches returned
0 results on OpenAlex and 0 on MathOverflow. GitHub results were mirrors:
the exact conjecture sentence returned 0 results, while the four results for
`A231548 antisigma` reproduced sequence data or the OEIS text. arXiv and
Semantic Scholar returned HTTP 429 on both attempts and are
`ASSUMED-UNVERIFIED`. No resolution was found in the bounded surfaces that
could be checked. This does not assert exhaustive literature coverage or
publication priority.

## Route

For every natural `n`, splitting the interval from one through `n` into
divisors and non-divisors gives
`antisigma(n) = n(n+1)/2 - sigma(n)`.

The factorization `332640 = 2⁵·3³·5·7·11` and multiplicativity of
the divisor-sum function give `sigma(332640) = 1451520`. Also
`332637 = 3 * 110879`, where `110879` is prime, so
`sigma(332637) = 443520`. Therefore
`antisigma(332640) = 55323399600`, while
`antisigma(332637) = 55323409683`. Thus
`antisigma(332640) < antisigma(332637)`, contradicting the conjecture at
`n = 332640`.

## Falsifier

A proof that `antisigma(n-3) <= antisigma(n)` for all natural `n >= 3`
would falsify this refutation. The kernel-checked instance at `n = 332640`
proves the strict reverse inequality, so such a proof would contradict the
formal result.

## Evidence

- Lean module:
  `D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- The recorded kernel type-checking time is 30 ms.
- The orchestrator's independent sieve over `3 <= n <= 400000` found
  violations exactly at `n = 332640` and `n = 360360`.
- The probe independently checked the same range and found the same two
  values, the factorizations of `332640` and `332637`, and the primality of
  `110879`.

The bounded sieve is supporting evidence only. The formal result uses the
single explicit instance `n = 332640` and makes no assertion about any other
input.

## Triage

`theorem`. The certified instance at `n = 332640` refutes the universal
gap-three conjecture. It asserts no corrected monotonicity statement and no
claim about other values of `n`.

## ASSUMED-UNVERIFIED

The arXiv and Semantic Scholar searches each returned HTTP 429 twice, so
those surfaces were not verified. The literature search is bounded and does
not establish exhaustive coverage or publication priority. The statement
that `332640` is the least violation is supported only within the checked
range `3 <= n <= 400000`; no unbounded leastness claim is made.
