---
slug: oeis-a140869-sundaram-triangle-complement-prime
bibkey: librandi2012a140869
doi: null
url: https://oeis.org/A140869
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime
---

# The A140869 Sundaram-type triangle complement

## Problem

OEIS A140869, NAME (`%N`, verbatim):

> T(m,n) = floor((2mn+m+n-2)/2), m >= n >= 1.

COMMENT (`%C`, verbatim; Vincenzo Librandi, Nov 18 2012):

> Conjecture: If h does not belong to the sequence, then 4*h+5 is prime.

The literal claim is
`∀ h, ¬(∃ m n, 1 ≤ n ≤ m ∧ T(m,n) = h) → 4h+5 prime`.
Here `T(m,n)` and the membership predicate use natural-number truncated subtraction
and division. On the stated domain `m ≥ n ≥ 1`, the numerator
`2mn+m+n−2` is at least `2`, so these operations agree with the intended expression.

## Motivation

The 2012 OEIS conjecture gives a universal complement-primality statement. The formal
result proves that every natural value outside the triangle has prime `4h+5`.

## Gap

The dated surfaces recorded from preregistration issue #7527 and the probe were OEIS
history revisions #1–#22, with revision #15 introducing the conjecture; no proof or
refutation is recorded there. Sibling entries A153085 and A144652 were checked, and
MathOverflow returned 0. arXiv and OpenAlex returned HTTP 429, and GitHub code search
returned HTTP 401; these rate-limited surfaces are ASSUMED-UNVERIFIED. The statement is
of Sundaram-sieve type, and no priority is claimed.

## Route

Use the contrapositive. If `4h+5` is odd composite, choose odd factors
`d·e = 4h+5` with `d,e ≥ 3`, write `d = 2a+1` and `e = 2b+1`, and order them so
`1 ≤ n ≤ m` after setting the smaller half-factor to `n` and the larger to `m`.
Expanding gives `4ab+2a+2b+1 = 4h+5`, hence `a+b` is even and the defining
equation yields `T(a,b) = h` after the corresponding ordering.

## Falsifier

An `h` outside the triangle for which `4*h+5` is composite would refute the theorem.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime.lean`.
- Main theorem: `librandi_a140869`, with std3 axiom closure.
- The orchestrator checked `h ≤ 3000`: 2881 triangle values and 120 outside values,
  with zero counterexamples outside the triangle.
- The converse is false at `h = 2`, `h = 8`, and `h = 12`; this dossier does not claim it.

## Triage

`theorem`

## ASSUMED-UNVERIFIED

The arXiv/OpenAlex HTTP 429 and GitHub code-search HTTP 401 surfaces are rate-limited;
the literature search is bounded, and no priority claim is made.
