---
slug: oeis-a400585-odd-cofactor-asymptotic
bibkey: oeis2026a400585
doi: null
url: https://oeis.org/A400585
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/A400585OddCofactorAsymptotic
---

# OEIS A400585: the odd-cofactor summatory asymptotic

## Problem

OEIS A400585, revision 22, defines

> a(n) = Sum_{d|n, n/d odd} binomial(d, 2).

Its FORMULA field states:

> Conjecture: Sum_{k=1..n} a(k) ~ 7*zeta(3)*n^3/48. - _Vaclav Kotesovec_, Oct 01 2026

The delivered statement keeps the source's full natural range. It defines the
natural divisor sum `a`, the real positive-prefix sum `S`, and the real series
`Z3 = sum_{q >= 0} 1/(q+1)^3`, then proves

```lean
Tendsto (fun N : ℕ => S N / ((7 * Z3 / 48) * (N : ℝ)^3))
  atTop (𝓝 1)
```

There is no parity, primality, or finite-range restriction. The natural value
at zero is harmless because the limit is at `atTop`.

## Motivation

The exact preregistration is [issue 15574](https://github.com/the-omega-institute/trureturing/issues/15574).
It records the quoted OEIS statement, the revision-22 source identity, the
full quantifiers, and the intended ratio-limit target before implementation.

## Gap

The source labels the summatory asymptotic as a conjecture. The bounded source
and object searches used for this delivery found no exact prior settlement in
the inspected OEIS, repository, pinned Mathlib, and identifier-search scope.
Those checks do not establish exhaustive publication priority or global
novelty. The generating-function and separate sigma-function comments in the
entry are outside the theorem.

## Route

Reindexing by the odd cofactor gives the finite sum of
`binomial(N / q + 1, 3)` over odd `q`. The binomial identity is
`6 * binomial(m + 1, 3) = m^3 - m`. After division by `N^3`, the pointwise
limit is `1/(6*q^3)` and the natural cubic reciprocal series supplies a
summable dominating function. Splitting the reciprocal series into even and
odd indices gives the constant `7*Z3/48`; its positivity permits the final
ratio normalization.

## Falsifier

An unbounded sequence of natural indices on which the displayed ratio stays
away from one, or a proved different limit for the same source statistic,
would refute this result. A finite disagreement with the OEIS data would not
refute an asymptotic statement.

## Evidence

The settling declaration is
`D5/S3/ArithSums/A400585OddCofactorAsymptotic.result`. Its D5 and Reg sources
compile with the pinned Lean and Mathlib toolchain. The public declarations
use the standard three axioms (`propext`, `Classical.choice`, and `Quot.sound`)
only. The retained Reg source is typed, `declared_validated`, and carries
current binding evidence; its continuation is recorded as `unknown`, which
records a residual without asserting undecidability or inexhaustibility.

The Scribe result node carries a `Proved` open-problem-resolution claim for
this dossier. The module introduces exactly the three source definitions and
the one result theorem; no D5 helper or frozen D5 dependency is added.

## Triage

First tier external OEIS conjecture; `admission_basis: open-problem-resolution`
under issue 15574. The definitions have no proof-shape obligation. The sole
result is honestly classified `proof_shape: bind-only`, with
`escape_witness: none`; its admission comes from settling the preregistered
external conjecture. Utility is none.

### What the settlement shows

The decisive proved mechanism is an exact reindexing by the odd cofactor. The
positive-prefix sum becomes a finite sum of
`binomial(N / q + 1, 3)` over odd `q`; the identity
`6 * binomial(m + 1, 3) = m^3 - m` gives the normalized pointwise limit
`1/(6*q^3)`. A cubic reciprocal series supplies a summable dominator, and the
even/odd split of that series gives `7*Z3/48`; its positivity then permits the
final ratio normalization.

The proved extent is the full ratio limit for every natural index sequence at
`atTop`, with the source's unrestricted quantifiers and no parity, primality,
or finite-range hypothesis. Computed evidence is limited to the finite source
prefix check (all 54 published revision-22 terms matched) and the bounded
source/object searches recorded for this delivery; these checks do not prove
an asymptotic statement or publication priority. The generating-function
comment, the separate sigma-function comment, effective error terms, secondary
terms, and broader divisor-weight generalizations are open in this delivery:
no Lean or independent evidence here settles them.

The settlement resolves the FORMULA conjecture quoted from A400585 in the
exact source statistic and records its source definition and coefficient. It
does not settle the entry's other comments or imply a literature-novelty or
first-publication claim; those questions remain outside this theorem.

## ASSUMED-UNVERIFIED

No exhaustive literature search, publication-priority claim, or external
independent proof is asserted. The source identification is tied to the OEIS
revision-22 entry and its citation-only Library note. The formal theorem is
the kernel-checked result stated above; the remaining OEIS comments are not
settled here.
