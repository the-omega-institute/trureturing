---
slug: oeis-a049473-kimberling-rounded-half-root-two-difference
bibkey: sloane2014a049473
doi: null
url: https://oeis.org/A049473
triage: theorem
motivation_gids:
  - D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference
---

# The differences of A049473 occupy two shifted Beatty sequences

## Problem

OEIS A049473, NAME (`%N`, verbatim):

> Nearest integer to n/sqrt(2).

Clark Kimberling's COMMENT (`%C`, verbatim, including the complete sentence
and attribution):

> Let s(n) = zeta(3) - Sum_{k=1..n} 1/k^3.  Conjecture:  for n >=1, s(a(n)) < 1/n^2 < s(a(n)-1), and the difference sequence of A049473 consists solely of 0's and 1, in positions given by the nonhomogeneous Beatty sequences A001954 and A001953, respectively.  - _Clark Kimberling_, Oct 05 2014

OEIS A001953, NAME (`%N`, verbatim):

> a(n) = floor((n + 1/2) * sqrt(2)).

OEIS A001954, NAME (`%N`, verbatim):

> a(n) = floor((n+1/2)*(2+sqrt(2))); winning positions in the 2-Wythoff game.

Writing `a(n) = round(n/sqrt(2))`, `lower(k) = floor((k+1/2)*sqrt(2))`,
and `upper(k) = floor((k+1/2)*(2+sqrt(2)))`, the literal proved clause says
that every `a(n+1)-a(n)` is zero or one, that it is one exactly when
`n = lower(k)` for some natural `k`, and that it is zero exactly when
`n = upper(k)` for some natural `k`.

The first clause of the same comment, the zeta(3) tail squeeze
`s(a(n)) < 1/n^2 < s(a(n)-1)`, is NOT claimed. No other property of A001953
or A001954 is claimed. The general complementarity of nonhomogeneous Beatty
sequences is classical 2-Wythoff theory and is cited as a literature
prerequisite, not claimed as a new result.

## Motivation

The difference clause identifies both the range and every position of the
adjacent differences of the nearest-integer sequence A049473. Proving all
three conjuncts settles the complete positional characterization rather than
only its bounded numerical pattern.

## Gap

On 2026-09-15, four shape-query groups were checked. arXiv exact phrases
returned 0 for all four. MathOverflow returned 0 except `2-Wythoff`, which
returned 5 items with no such characterization. OpenAlex and Crossref
returned general theory only, including Cassaigne-Duchêne-Rigo and similar
work. Google Scholar was robot-challenged and Semantic Scholar returned HTTP
429; both are recorded `ASSUMED-UNVERIFIED`.

The located literature includes Connell's generalization of Wythoff's game,
Larsson's work on p-complementary Beatty sequences, and
Cassaigne-Duchêne-Rigo's nonhomogeneous Beatty theory. None of the checked
surfaces states the A049473 round-difference characterization. These searches
do not establish exhaustive literature coverage, and no priority claim is
made.

## Route

1. Rewrite real rounding as the floor of `n/sqrt(2) + 1/2`, and bound its
   adjacent increment between zero and one.
2. Characterize an increment of one by the unique integer crossed between
   two adjacent arguments. Irrationality of the shifted sqrt-two multiple
   excludes an endpoint equality and gives exactly the `lower` positions.
3. Use `1/(2+sqrt(2)) = 1-1/sqrt(2)` to derive the zero-position inequalities
   directly, giving exactly the `upper` positions.
4. The shifted complementarity organizing the two position families is the
   classical 2-Wythoff fact; the live jump and zero-position equivalences are
   proved in the module rather than imported from the homogeneous Mathlib
   Rayleigh theorem.

## Falsifier

Any natural `n` whose adjacent difference is outside `{0,1}` contradicts the
first conjunct. A one-difference position absent from `lower`, a `lower`
position without a one difference, a zero-difference position absent from
`upper`, or an `upper` position without a zero difference contradicts one of
the two iff conjuncts. The kernel-checked result quantifies over every
natural `n`.

## Evidence

- Lean module:
  `D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile before import minimization: wall time 24.89 seconds, type
  checking 76.5 milliseconds, and maximum resident set size 2,978,267,136
  bytes.
- Kernel profile after import minimization: wall time 16.17 seconds, type
  checking 54.6 milliseconds, and maximum resident set size 2,132,492,288
  bytes.
- The probe used Decimal precision 100 for `n=0..50000`: differences were
  exactly `{0,1}`; the 35,356 one-positions and the `lower` image had empty
  set differences both ways; the 14,645 zero-positions and the `upper` image
  likewise had empty set differences both ways.
- The bounded scan carries no proof. The floor inequalities, irrational
  endpoint exclusion, and shifted zero-position derivation carry the
  universal proof.

## Triage

`theorem`. Kimberling's difference-sequence clause is proved for every
natural index; the resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

Google Scholar result inspection was blocked by a robot challenge, and
Semantic Scholar returned HTTP 429. Literature completeness is unverified;
no exhaustive-literature or priority claim is made. The bounded scan is not
a proof and does not verify the universal statement.
