---
slug: oeis-a229140-stephan-least-coordinate-distinctness-refutation
bibkey: stephan2013a229140
doi: null
url: https://oeis.org/A229140
triage: theorem
motivation_gids:
  - D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.result
---

# Refutation of Stephan's A229140 least-coordinate distinctness conjecture

## Problem

OEIS A229140 states (verbatim):

> %N A229140 Smallest k such that k^2 + l^2 = n-th number expressible as sum of two squares (A001481).
> %C A229140 Conjecture: the values between two zeros are always distinct from each other.
> %A A229140 _Ralf Stephan_, Sep 15 2013
> %O A229140 1,6

The literal refuted statement is: for every pair `L<R` of representable
natural values with least first coordinate zero and with no intervening value
having least first coordinate zero, distinct representable values strictly
between `L` and `R` have distinct least first coordinates.

The relation `IsLeastCoord m x` states that `m=x^2+y^2` for some natural `y`
and that no natural `x'<x` is the first coordinate of any such representation.
Consequently, `IsLeastCoord m 0` is exactly the assertion that `m` is a
square: the representation clause becomes `m=y^2`, and the exclusion clause
is vacuous because no natural number is below zero. In `claim`, the two
endpoint hypotheses say that `L` and `R` are zero values, `L<R` orders them,
and the universal no-zero hypothesis says they are consecutive. The final
quantifiers assert the distinctness of least coordinates for every two
distinct intermediate values.

This result does not claim an enumeration of A001481; the identities added by
Zhuorui He in 2025,
`a(n) = sqrt(A001481(n)-A385236(n)^2)`,
`a(n) = A328803(n) - A385236(n)`, or
`a(n) = A064875(A001481(n))`; any property of A064875, A385236, A328803,
A283303, or A283304; whether the conjecture holds on any other interval; or
exhaustive literature coverage.

## Motivation

The conjecture first appeared in OEIS revision #8 on September 17, 2013 and
has remained unsettled for 13 years. Its counterexample is already visible in
the entry's own linked b-file at lines `216 0`, `218 12`, `231 12`, and
`233 0`. These rows correspond to the consecutive zero endpoints 625 and 676
and the intermediate values 628 and 673, both assigned the value 12. The
conjecture was never re-checked against the data linked by the entry itself.
No priority claim is made.

## Gap

The literature check on September 15, 2026 found zero OpenAlex results for
the exact A-number and zero for the exact conjecture sentence; its top ten
structural-query results were irrelevant. Crossref returned zero exact
A-number results, and the top ten phrase and structural results were
irrelevant. Direct arXiv searches for `A229140`, the exact sentence, and
`least representation coordinate` with `sum of two squares` each returned
zero. The MathOverflow API returned zero for all three query shapes. GitHub
code search returned zero for the exact phrase. The cross-referenced entries
A064875, A385236, A328803, A283303, and A283304 were each read and contain
definitions and cross-formulas but no proof or refutation of the conjecture.

These are bounded searches. Google and DuckDuckGo were CAPTCHA-blocked, Bing
returned nothing relevant, Semantic Scholar returned HTTP 429, and GitHub's
A-number search was capped at 100 substring-heavy results. The finding is
`not-found-in-searched-scope`, not exhaustive literature coverage, and no
publication-priority claim is made.

The OEIS revision-history page records revision #8 by Ralf Stephan at Tue Sep
17 03:55:26 EDT 2013 as the first revision containing the word `distinct`.
Current revision #39 at Tue Sep 23 23:41:09 EDT 2025 still carries the COMMENT
without a settlement.

## Route

Four finite obligations refute the universal claim:

1. The displayed representations are `628=12^2+22^2` and
   `673=12^2+23^2`.
2. For each of 628 and 673, direct finite exclusion rules out every first
   coordinate `x'=0,...,11`.
3. No natural square lies strictly between the consecutive squares 625 and
   676.
4. The endpoint representations `625=0^2+25^2` and `676=0^2+26^2` witness
   the two zero values.

The second obligation makes 12 the least first coordinate for both distinct
intermediate values. The third and fourth make 625 and 676 consecutive zero
values. Substituting these facts into the universal statement produces a
contradiction.

## Falsifier

A proof of the literal universal `claim` would falsify this refutation. At the
certificate level, a representation of 628 or 673 with first coordinate below
12, a square strictly between 625 and 676, or failure of either displayed
endpoint representation would break one of the finite obligations. The Lean
theorem instead proves `Not claim` from all four obligations.

## Evidence

- Lean module:
  `D5/S3/PrimeForms/StephanLeastCoordinateDistinctnessRefutation.lean`.
- Public declarations: `IsLeastCoord` and `claim` are definitions, and
  `result : Not claim` is a theorem. There are no private declarations.
- `#print axioms` reports `[propext]` for each definition and exactly
  `[propext, Classical.choice, Quot.sound]` for `result`; every declaration is
  within std3.
- The canonical Lean report identifies `claim` as
  `sha256:9ecf84ff244ae3e07b61d766e36b3f8daf799a308b2d43ce37a007a7917de560`
  and `result` as
  `sha256:3447d7a4781648c125118bceda5411ae7aaa45eb966856313ea2887e87e05d9b`,
  and records the result as a closed negation of the claim.
- The profiled Lean process took 7.64 seconds wall time and 55.4 milliseconds
  of cumulative type checking, with maximum resident set size
  1,495,990,272 bytes.

An independent reconstruction enumerated `x,y` in `[0,800]`, which is
exhaustive for all sums below 640000. The 10000th generated representable
value is 39592, and 141068 representable values lie below the ceiling. All
10000 official b-file terms were compared with the reconstructed
least-coordinate map, with zero mismatches. The first violation has left zero
`(216,625)`, duplicate pair `(218,628,12)` and `(231,673,12)`, and right zero
`(233,676)`.

The official b-file itself displays the corresponding values at lines
`216 0`, `218 12`, `231 12`, and `233 0`.

## Triage

`theorem`. The certified values 628 and 673 refute the literal universal
distinctness assertion between the consecutive zero values 625 and 676. The
result settles only that conjecture.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. Google and DuckDuckGo were
CAPTCHA-blocked, Bing returned nothing relevant, Semantic Scholar returned
HTTP 429, and GitHub's A-number search was capped at 100 substring-heavy
results. None of these bounded surfaces supports an exhaustive-literature or
priority claim.
