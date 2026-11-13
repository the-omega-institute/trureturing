---
slug: oeis-a177775-ordinary-coefficient-parity
bibkey: hanna2026a177775
doi: null
url: https://oeis.org/A177775
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/DiagonalOrdinaryParity.result
---

# Hanna's A177775 ordinary-coefficient parity conjecture

## Problem

Paul D. Hanna, OEIS A177775, conjecture comment:

> Conjecture: a(n) is odd iff n is a power of 2.

The [immutable source](https://raw.githubusercontent.com/oeis/oeisdata/501c6189fe17530d95e5a4f90dbca228feb5713d/seq/A177/A177775.seq)
has SHA-256 `adff5528b1f3f6030f713ec4603f243ddb0a3442ccdf02a08880f0f180403eac`.
The conjecture comment is from May 19, 2026, in approved revision 10 of May 20,
2026. The entry's May 13, 2010 author date does not date this conjecture.
The citation-only [source note](../Library/RecurrenceComposition/hanna2026a177775.md)
retains the source locators and normalization; [preregistration #30066](https://github.com/the-omega-institute/trureturing/issues/30066)
fixes the complete target.

Let $G\in\mathbb Z[[X]]$ satisfy $[X^0]G=0$ and $[X]G=[X^2]G=1$.
Set $G^{[0]}=X$ and $G^{[m+1]}=G^{[m]}(G(X))$. For every natural $n>2$,
require $[X^n]G^{[n]}=[X^n]G^{[n-1]}$. The source's recursive program and
revised seed `[0,1,1]` supply the initial values; offset `1,3` adds no seed.
The conjecture asserts

\[
\forall n\in\mathbb N,\quad n\ge1\Longrightarrow
\bigl(\operatorname{Odd}([X^n]G)\iff\exists k\in\mathbb N,\ n=2^k\bigr).
\]

| Source clause | Lean counterpart |
| --- | --- |
| Integer series and the three initial coefficients | `DiagonalIterateEven.generatingSeries`, `generating_equation` |
| Composition, starting at $X$ | `DiagonalIterateEven`'s imported `iterate` |
| Adjacent-iterate equality at every $n>2$ | `generating_equation` and `generating_unique` |
| Ordinary coefficient $[X^n]G$ | `PowerSeries.coeff n generatingSeries` in `DiagonalOrdinaryParity.result` |
| Every $n\ge1$, both implications, including $n=1=2^0$ | The complete telescope and iff of `result` |

The integer construction and uniqueness are proved by the existing supplier;
existence and integrality are not hypotheses of the resolution. The source
programs themselves are not formalized. `DiagonalIterateEven.a` is the
different diagonal sequence A395842 and is not this target.

## Motivation

This is a tier 1 external OEIS conjecture. The complete ordinary-coefficient
assertion is obtained by composing frozen characteristic-two suppliers.

## Gap

The bounded source and literature screen recorded in #30066 found no proof
in the inspected OEIS revision, repository ownership search, arXiv, Crossref,
MathOverflow or Math.SE identifier searches. Merged PR #6777 settles
A395842 and explicitly excludes A177775. The captured dev contains no
A177775 settlement. Identifier-free papers, unnamed ongoing work and
worldwide publication priority are outside this screen.

## Route

Write $P$ for `CubicFifteenSubstitutionParity.powerTwoSeries` over
$\mathbb Z/2\mathbb Z$. Its coefficient at $n$ is the indicator of
$\exists k\in\mathbb N,\ n=2^k$. The first part of `thue_series_equation`
and characteristic two yield $P+P^2=X$. The supplier's inverse series $H$
has zero constant coefficient and satisfies $H+H^2=X$. Applying the existing
`quadratic_unique` gives $H=P$. The existing `mod_two_identity` identifies
the coefficientwise reduction of $G$ with $H$. Applying the coefficient
map and `ZMod.intCast_eq_one_iff_odd` proves the stated iff.

## Falsifier

An index $n\ge1$ for which exactly one of oddness of $[X^n]G$ and existence
of a natural $k$ with $n=2^k$ holds would refute this claim. Changing the
normalization, replacing ordinary coefficients with diagonal coefficients,
or imposing a degree bound changes the problem.

## Evidence

The mathematical source is `D5/S1/Recurrence/Parity/DiagonalOrdinaryParity.lean`,
with sole public theorem `result`. Its owning Scribe carries the exact
statement and `OpenProblemResolutionClaim` with kind `Proved`.
`Reg/D5/S1/Recurrence/Parity/DiagonalOrdinaryParity.lean` retains the full
source-equivalence audit with continuation `.unknown`. This residual marker
does not assert undecidability or inexhaustibility.

The existing suppliers expose only their original private declarations;
their original types and proofs are retained. Their visibility change is
canonically repinned. The unfinished full-telescope `quadratic_unique`
source-role audit is disclosed in [#30076](https://github.com/the-omega-institute/trureturing/issues/30076);
it is not `declared_validated`. Audit evidence and mathematical proof remain
distinct.

## Triage

The exact conjecture is proved by `result`, with `proof_shape: bind-only`
and sole `admission_basis: open-problem-resolution` under #30066. There is
no escape-witness credit. No corresponding theory volume or digestion atom
is identified; the target uses `deposit-uncovered`.

## ASSUMED-UNVERIFIED

The source-to-Lean correspondence is a semantic assessment, distinct from
kernel verification. The bounded search does not certify worldwide novelty
or publication priority. External-problem delivery credit requires the
independent final reviews, required checks and actual merge.
