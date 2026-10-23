---
slug: oeis-a394399-twin-prime-sigma-gcd-three
bibkey: oeis2026a394399
doi: null
url: https://oeis.org/A394399
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.result
---

# Twin-prime sigma-gcd three forces twice a square

## Problem

For every natural number k, if k-1 and k+1 are prime and gcd(k, sigma(k))=3, then there is a natural number m with k=2m². Here sigma(k) is the sum of positive divisors.

## Motivation

This is the A394399 conjecture supplied in preregistration #15003. It characterizes the shape of a twin-prime center satisfying the specified gcd condition.

## Gap

The target was the universal twice-square implication, including the small centers and natural subtraction. Divisor-sum parity alone leaves a square alternative that must be excluded.

## Route

The reused twin-center theorem makes k even. The gcd condition then makes sigma(k) odd. The existing divisor-sum parity criterion gives a square or twice a square. In the square branch, k=s² and k-1=(s-1)(s+1); primality forces k=4. But sigma(4)=7 and its gcd with four is one. The twice-square branch is therefore forced.

## Falsifier

A natural k with prime neighbors, gcd(k, sigma(k))=3, and no natural m satisfying k=2m² would falsify the statement.

## Evidence

- Lean module: `D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.lean`.
- Exact proposition: `claim`; universal proof: `result : claim`.
- Reused frozen declarations: `TwinPrimeSigmaGcdDivisibility.even_center` and `KrizekTriangularSquareSigmaParity.sigma_odd_iff_square_or_twice_square`.
- The proof is unbounded and does not assert that qualifying centers exist infinitely often.

## Triage

- [proved] The universal statement in the Problem section.
- [open] Whether infinitely many centers satisfying these conditions exist. This involves unresolved twin-prime infinitude and the additional sigma-gcd restrictions; twin-prime infinitude alone does not settle those restrictions.

## ASSUMED-UNVERIFIED

The OEIS attribution and the literature status are supplied by the preregistration. No network is available to independently reread the entry or extend its literature search. First-publication priority is not a kernel-checked conclusion. The Lean claim retains exactly the supplied quantifiers and hypotheses.
