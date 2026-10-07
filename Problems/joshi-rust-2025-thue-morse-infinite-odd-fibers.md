---
slug: joshi-rust-2025-thue-morse-infinite-odd-fibers
bibkey: joshirust2025monochromatic
doi: 10.1016/j.tcs.2025.115391
url: https://arxiv.org/html/2501.05830v2#S3.Thmtheorem7
triage: theorem
motivation_gids:
  - D5/S1/Words/ThueMorseMapFirstStart
---

# Infinite odd fibers of Thue-Morse global maxima

## Problem

Joshi and Rust, arXiv:2501.05830v2, Section 3.2.1, Question 3.7,
second clause asks: “Are there infinitely many values of n for which
O_max(n)=∞?” The first and third clauses are outside this target.

The staged claim is that the set of natural lengths n for which the set
of positive odd differences d satisfying ExactMax(d,n) is infinite is
itself infinite. ExactMax requires a start attaining length n and a
universal bound on every monochromatic AP length at every natural start.
MAP and the actual zero-indexed thueMorse are reused from the existing
Words sources. This covers both colors and the entire infinite word.

## Motivation

This question concerns the distribution of actual progression maxima,
rather than one explicit family of long progressions. The existing
first-start result supplies the actual word, MAP and general dyadic
identities. The latter are shared through ThueMorseDyadic.

## Gap

Unbounded attained lengths alone do not give infinite exact-max fibers.
For each lower bound, one needs infinitely many distinct odd differences,
a uniform finite upper bound over all starts, and actual maximum attainment.

## Route

Fix odd m>=3 and put M=2^m, c=M^2+M+1, B=2^(4m+1), a=c(M^2-1),
U=2B+2. Base-M digits give a true triple at a,a+c,a+2c inside one
B block, and t(cj)=t(j) for j<M. Coprimality of B and c transports
the triple into every U-letter c-spaced window. No such window is a
color translate of consecutive Thue-Morse letters, since those contain
no monochromatic triple.

For R=2^k>=max(2U+1,M) and d=cR+1, the single-carry split bounds every
monochromatic progression at every start by 2U. Start zero attains M.
The finite nonempty set of attained lengths has an actual maximum in
[M,2U]. Infinite pigeonhole across distinct positive odd differences
gives an infinite exact-max fiber at some n>=M. Unbounded odd exponents
yield infinitely many such lengths.

## Falsifier

Only finitely many natural lengths with infinite positive odd exact-max
fibers would refute the claim. A missing attaining start, a longer
progression at any start or color, or use of a different word convention
would invalidate the source correspondence.

## Evidence

- Formal source: D5/S1/Words/ThueMorseMapInfiniteFibers.lean.
- Public declarations: ExactMax, claim, result.
- ExactMax(d,n) requires an attaining start and bounds every AP length
  at every natural start. Both Boolean colors are unrestricted.
- The public import check verifies the expanded statement, explicit
  color quantifiers and the Scribe unbounded-quantifier formulation.
- The result's axiom closure is propext, Classical.choice, Quot.sound.
- Exact source: https://arxiv.org/html/2501.05830v2#S3.Thmtheorem7.

## Triage

Theorem: the Lean result establishes the exact second clause. Its mechanism
combines replicated triples, residue transport, dyadic carry control,
finite attainment and infinite pigeonhole. The selected exact maxima are
not given an explicit formula. The first and third clauses, a classification
of all infinite fibers, and an explicit maximum formula remain unproved
by this result. No other paper result is used as a consequence of this
clause in the formal proof.

## ASSUMED-UNVERIFIED

Compilation status and exact source hashes belong to the staging receipts.
Integration, canonical gates and external acceptance are controller-owned.
The published question and library suppliers are source checked; no
exhaustive later-literature audit is claimed. Worldwide novelty, priority
and official acceptance are unverified.
