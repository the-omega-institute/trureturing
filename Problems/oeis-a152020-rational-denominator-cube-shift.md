---
slug: oeis-a152020-rational-denominator-cube-shift
bibkey: cicuttin2017a152020
doi: null
url: https://oeis.org/A152020
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/RationalDenominatorCubeShift
---

# The rational-denominator cube shift in A152020

## Problem

OEIS A152020, NAME:

> Denominator of 8/(9*n^2) divided by 9.

FORMULA (Andrew Howroyd, Jul 25 2018):

> a(n) = n^2/gcd(n^2, 8). - _Andrew Howroyd_, Jul 25 2018

FORMULA (Andres Cicuttin, Sep 19 2017):

> Conjecture: a(n) = denominator((n-2)^3/n^2). - _Andres Cicuttin_, Sep 19 2017

## Motivation

This OEIS conjecture gives a closed expression for the reduced denominator
sequence at every index in its offset range. Proving the identity resolves
the stated conjecture and identifies its arithmetic mechanism.

## Gap

The preregistration search on 2026-09-13 checked OEIS, zbMATH Open, Crossref,
arXiv, OpenAlex autocomplete, the MathOverflow API, and GitHub repository and
commit searches. A proof or refutation was not found in the checked surfaces.
GitHub code search required authentication, while OEIS revision endpoints
returned a challenge or 404, so those two surfaces were not fully checked.
This bounded search does not establish exhaustive literature coverage or
first-publication priority.

## Route

For integers `p` and nonzero `q`, the positive reduced denominator of `p/q`
is `|q|/gcd(|p|,|q|)`. Applying this formula to both rational expressions
reduces the theorem to
`gcd(n^2,(n-2)^3) = gcd(n^2,8)` for `n >= 2`. The identity follows by the
residue class of `n` modulo 4: the gcd is 1 when `n` is odd, 4 when
`n congruent to 2 modulo 4`, and 8 when `4` divides `n`. The index `n = 1`
is evaluated separately. An integer `natAbs` bridge identifies the signed
cube numerator with the natural subtraction used in the gcd argument.

## Falsifier

Any positive index `n` for which the two reduced denominators differ would
refute the claim. A failure of the residue-class gcd identity, the exact
division by 9 on the left, or the signed `natAbs` conversion would also
invalidate the proof route. The finite checks below support but do not
replace the universal proof.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/RationalDenominatorCubeShift.lean`.
- Main theorem: `cicuttin_a152020`.
- Public definition: `a`, defined using `Rat.den` and natural-number division
  by 9.
- The theorem has exactly the std3 axioms: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The orchestrator supplied an exact `fractions.Fraction` check for
  `1 <= n <= 100000`: zero mismatches, and every left reduced denominator
  was divisible by 9.
- The probe supplied the same exact range split into the three proof classes:
  50000 odd indices, 25000 indices congruent to 2 modulo 4, and 25000 indices
  divisible by 4.

## Triage

`theorem`. The Lean theorem proves Cicuttin's full denominator identity for
every positive natural index, matching the OEIS offset.

## ASSUMED-UNVERIFIED

The OEIS quotations, attributions, dates, bounded literature-search results,
and exact finite-check readings were supplied by the preregistration issue,
the orchestrator, and the probe seat. This implementation seat did not
independently repeat the external searches or numerical checks. No exhaustive
literature or priority claim follows. Source-to-Lean identification is not
itself a kernel-checked fact.
