---
slug: oeis-a103585-sloping-binary-period-refutation
bibkey: cloitre2005a103585
doi: null
url: https://oeis.org/A103585
triage: theorem
motivation_gids:
  - D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation
---

# Refutation of the A103585 period-43 comment

## Problem

OEIS A103585, NAME (verbatim):

> Consider numbers k such that (A102370(k)-k)/2 = 1; read them mod 4 to get the sequence.

Ralf Stephan's COMMENT of May 18, 2007 (verbatim):

> Sequence appears to have period 43.

For natural numbers, define
`s(k) := k + Sum_{m in Icc(1,k+1)} (if (k+m) mod 2^m = 0 then 2^m else 0)`,
the finite form of the A102370 formula; define `P(k) := (s(k) = k+2)`; and
define `A(i) := nth(P,i) mod 4`. Thus `A` is zero-indexed and OEIS `a(m)`
equals `A(m-1)`. The literal refuted statement is
`for every natural i, A(i+43) = A(i)`.

The definition of A102370, the `%N` definition of A103585, any true period,
and eventual aperiodicity are not claimed or assessed.

## Motivation

Stephan's comment asserts a universal period. Two entries exactly 43 places
apart with different residues suffice to refute that literal assertion.

## Gap

Checks dated September 14, 2026 found no settlement in the current OEIS entry
or its checked history. Applegate, Cloitre, Deléham, and Sloane's 2005 JIS
paper 05.3.6 lists A103585 among the sequences it concerns but contains zero
occurrences of "period 43" and predates Stephan's 2007 comment.

An exact MathOverflow API search returned 0 items. A Crossref bibliographic
search returned 0 relevant A103585, period-43, or sloping-binary matches among
20 returned works. The arXiv API returned HTTP 429, so that surface is
`ASSUMED-UNVERIFIED`. These bounded checks establish neither exhaustive
literature coverage nor publication priority, and no priority claim is made.

## Route

Let `P(k)` mean `s(k)=k+2`. Kernel computation gives
`Nat.count P 383 = 128` and `P(383)`. The theorem `Nat.nth_count` therefore
gives `Nat.nth P 128 = 383`, so `A(128)=383 mod 4=3`. Likewise,
`Nat.count P 513 = 171` and `P(513)` give `Nat.nth P 171 = 513`, so
`A(171)=513 mod 4=1`. Since `171=128+43`, the instance `i=128` contradicts
the period-43 claim. In OEIS one-based indexing, this is `a(129)=3` and
`a(172)=1`.

## Falsifier

A proof of the literal universal `claim` would falsify this refutation. The
result instead supplies the finite ranking obstruction at zero-based index
128.

## Evidence

- Lean module:
  `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.lean`.
- Main theorem: `result : Not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The profiled Lean process took 41.62 seconds wall time and 15,286.716
  milliseconds of cumulative type checking, with maximum resident set size
  7,271,268,352 bytes.
- The finite certificate proves the two counts and selector facts, then uses
  `Nat.nth_count` to identify the two entries. No private declaration is
  present.

The orchestrator independently checked that the finite formula for `s`
matches the displayed A102370 data, that the first 20 values selected by `P`
and reduced modulo four match A103585, and that the two counts are 128 and
171. These bounded computations support the certified instance; they do not
assert a classification of all failures or a true period.

## Triage

`theorem`. The finite ranking certificate at `i=128` refutes the literal
period-43 comment. No publication-priority claim is made.

## ASSUMED-UNVERIFIED

The bounded scan beyond the certified instance and historical openness after
the checked OEIS, JIS, MathOverflow, and Crossref surfaces are
`ASSUMED-UNVERIFIED`. The arXiv surface is also `ASSUMED-UNVERIFIED` because
its API returned HTTP 429.
