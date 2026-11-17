---
slug: finch-2026-conjecture-23-capture-offset
bibkey: finch2026quadraticrecurrences
doi: null
url: https://arxiv.org/abs/2610.34300v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation
---

# Finch Conjecture 23: the capture/preperiod offset

## Problem

Steven Finch, *Three Quadratic Recurrences Modulo 3: What We Can Prove and
What We Can Guess*, arXiv:2610.34300v1, Conjecture 23, p. 9:

> For every k congruent to 2 or 3 modulo 4 with N_A(k)=4, z(k)-μ_A(k)=6.

The final Addendum fixes k≥2. Recurrence (A) has values in Z/3, initial
zeros x(1),...,x(k-1), x(k)=1, and x(n)=x(n-1)+x(n-k)^2 for n≥k+1.
A run with g gaps starts at r≥k+1, has g≥1, zeros at r,r+4,...,r+4g,
and no other zeros between its endpoints. With G=ceil((k-1)/4), z is the
least endpoint of a G-gap run. The preperiod is the least natural μ such
that x(n+4)=x(n) for all n>μ. N_A(k) is the least positive eventual period.

## Motivation

The conjecture gives a uniform offset between two independently defined
least indices. Its stated domain contains a purely periodic boundary case.
The binding statement and source conventions are specified in #23615.
The small-case refutation makes no originality or priority claim.

## Gap

Repository searches in D5, Blueprint, Problems, Library and existing theory
located no prior exact settlement. Pinned Mathlib provides ZMod, IsLeast and
natural remainder arithmetic; periodic-point results concern an endomorphism
and do not supply these source-specific least capture data. Authenticated
GitHub code searches for FinchConjecture23, 2610.34300 and IsCapturePoint
with ZMod in Lean returned zero matches. The exact-target issue remains open,
and current target-issue PR search returned no matches. These bounded
searches do not establish global absence or priority. Source access succeeded.

## Route

Set x(n) by n mod 4: residues 0,1,2,3 give 2,0,1,1. The positive-index
block is therefore (0,1,1,2). Four residue cases verify the recurrence for
every n≥3. Period four holds for every index. For any eventual threshold μ,
choose n=4(μ+1)+1; this n exceeds μ and its value is zero, whereas the
values at n+1,n+2,n+3 are nonzero. Hence no positive period below four can
be eventual. The least positive eventual period is exactly four.

Four-periodicity from the first positive term makes μ=0 a member of the
preperiod set; it is least because every member is natural. At k=2, G=1.
The run from 5 to 9 qualifies, including the nonzero interior values at
6,7,8. Every allowed earlier start is 3 or 4, where x is nonzero, so every
qualifying endpoint is at least 9. Thus z=9 is the least capture endpoint.
The integer difference is 9, which contradicts the asserted value 6.

## Falsifier

A failure of the all-index recurrence, a smaller positive eventual period,
a smaller capture endpoint under r≥3, or failure of four-periodicity from
the first term would invalidate this witness. Each obligation is present in
the Lean proof; no finite prefix or default minimum replaces it.

## Evidence

The formal source is
`D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.lean`, namespace
`Trureturing.OpenProblems.FinchConjecture23CaptureOffset`.
Its designated theorem is literally `result : Not claim`. The eight source
definitions preserve the binding conventions in #23615. The proof uses an
actual source realization at k=2 and the three IsLeast certificates, then
uniqueness of least elements forces z=9 and μ=0.

## Triage

`theorem`. The result addresses only the original universal Conjecture 23.
It proves no infinite exceptional family, corrected k≥3 law, positive-
preperiod law, Conjecture 14 or Remark 20. The explicit least-μ definition
is meaningful here; the source's last-disagreement equivalence requires a
separate convention for purely periodic sequences.

## ASSUMED-UNVERIFIED

Global literature completeness, originality and publication priority are
unverified. Bounded repository and external-code searches do not establish
those claims. The unavailable predecessor checkpoint is not proof evidence.
