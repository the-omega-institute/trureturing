---
slug: oeis-a394757-sigma-gcd-two-or-three
bibkey: oeis2026a394757
doi: null
url: https://oeis.org/A394757
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.result
---

# Prime twin-center sigma-gcd values are two or three

## Problem

For every natural number k, if k-1 and k+1 are prime and gcd(k, sigma(k)) is prime, then gcd(k, sigma(k))=2 or gcd(k, sigma(k))=3.

## Motivation

This is the second A394757 conjecture supplied in preregistration #15004. It determines the possible prime gcd values, complementing the existing divisibility-by-18 theorem.

## Gap

The existing divisibility theorem constrains k but does not identify its prime sigma-gcd. The odd divisor-sum branch requires three to divide sigma(k).

## Route

An even sigma(k) gives two dividing the prime gcd, so that gcd equals two. For odd sigma(k), the existing divisibility-by-18 result excludes small centers, and the shared square exclusion gives k=2t² with t nonzero. Write t=2^b r with r odd. Coprime multiplicativity yields sigma(k)=sigma(2^(2b+1)) sigma(r²). The existing geometric-sum formula identifies the first factor as 2^(2b+2)-1. Since 4^(b+1) is congruent to one modulo three, this factor is divisible by three. The existing three_center theorem gives three dividing k. Thus three divides the prime gcd and that gcd equals three.

## Falsifier

A natural twin-prime center whose sigma-gcd is prime and differs from both two and three would falsify the statement.

## Evidence

- Lean module: `D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.lean`.
- Exact proposition: `claim`; universal proof: `result : claim`.
- Reused frozen declarations: `TwinPrimeSigmaGcdDivisibility.even_center` and `KrizekTriangularSquareSigmaParity.sigma_odd_iff_square_or_twice_square`.
- The proof is unbounded and does not assert that qualifying centers exist infinitely often.

## Triage

- [proved] The universal statement in the Problem section.
- [open] Whether infinitely many centers satisfying these conditions exist. This involves unresolved twin-prime infinitude and the additional sigma-gcd restrictions; twin-prime infinitude alone does not settle those restrictions.

## ASSUMED-UNVERIFIED

The OEIS attribution and the literature status are supplied by the preregistration. No network is available to independently reread the entry or extend its literature search. First-publication priority is not a kernel-checked conclusion. The Lean claim retains exactly the supplied quantifiers and hypotheses.
