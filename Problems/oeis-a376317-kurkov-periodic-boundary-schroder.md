---
slug: oeis-a376317-kurkov-periodic-boundary-schroder
bibkey: oeis2024a376317
doi: null
url: https://oeis.org/A376317
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.result
---

# Kurkov's periodic boundary recurrences and the large Schroder diagonal

## Problem

Mikhail Kurkov's OEIS A376317, revision 25, states:

> Conjecture: cases f(n) = n mod 2 and f(n) = [(n mod 3) > 0] both gives A006318.

The source array is the natural recursion with `P(0,m)=1`, the positive-row
branch `P(n,m)=P(n-1,m)` for `m<=n`, and
`P(n,m)=P(n,m-1)+P(n-1,m+f(m-n))` otherwise. The zeroth-row clause has
priority. The settled statement keeps both shifts in one proposition:

```lean
∀ n : ℕ,
  P f2 (n + 1) (n + 1) = Nat.largeSchroder n ∧
  P f3 (n + 1) (n + 1) = Nat.largeSchroder n
```

Here `f2 d = d % 2` and `f3 d = 0` exactly when `d % 3 = 0`, and
`Nat.largeSchroder` is A006318. The statement includes `n=0`; no alternate
array, truncation, integrality premise, or second count is substituted.
A376388 repeats this same conjecture and is not a second resolution.

## Motivation

The two periodic source shifts have the same diagonal sequence. The result
answers the complete unbounded source question, rather than a finite prefix.
Its admission basis is `open-problem-resolution`; utility is none.

## Gap

The source reading and bounded literature screen are recorded in
[`Library/RecurrenceComposition/oeis2024a376317.md`](../Library/RecurrenceComposition/oeis2024a376317.md).
That note records the exact OEIS revision, the repeated A376388 wording, the
arXiv metadata queries, the pinned LeanOpenProblems corpus screen, and the
targeted third-party Lean readings. No exact proof was found in that scope.
The scope does not establish worldwide openness, priority, or exhaustive
absence of an unpublished proof.

The preregistration and settlement record remain in issue
[#23318](https://github.com/the-omega-institute/trureturing/issues/23318).
Its sole proved terminal comment is
[#6481166931](https://github.com/the-omega-institute/trureturing/issues/23318#issuecomment-6481166931);
the source reconstruction disclosure is
[#6480851425](https://github.com/the-omega-institute/trureturing/issues/23318#issuecomment-6480851425).
No new mathematical terminal issue is introduced by this dossier.

## Route

The Lean definition preserves the source's lexicographic recursion, including
the below-diagonal branch. Writing `C_f(n,d)=P_f(n,n+d)` yields the boundary
and step equations used by the proof. A coefficient-identification induction
over rational formal power series then reduces the diagonal to the coefficient
of a family `H`.

For the period-two shift, the family alternates between
`(1+xS)S^j` and `S^(j+1)`, where `S` is Mathlib's large Schroder series. For
the period-three shift, `R=(S^2+S)/2` supplies the three residue branches.
The quadratic Schroder-series identity verifies both systems, and coefficient
extraction gives the two natural equalities. All exponents are natural; no
integrality assumption on `R` is used.

## Falsifier

Any natural `n` for which either diagonal differs from `Nat.largeSchroder n`
refutes the conjunction. Changing the zeroth-row priority, the positive-row
branch, or either periodic shift changes the source question and is not a
counterexample to this statement.

## Evidence

The frozen declaration is
`D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.result`, with canonical
exposition in the corresponding Blueprint Scribe. Its scoped Lean report
records the standard closure `{propext, Classical.choice, Quot.sound}` and no
additional axiom or `sorry`. The Reg mirror compiles, but its current audit
readout remains `declared_unresolved` (`IE-C050`, `unclassified_form`,
`source.statement_reconstruction`) under the disclosure in
[#23318](https://github.com/the-omega-institute/trureturing/issues/23318#issuecomment-6480851425).
That audit limitation does not alter the kernel-checked theorem or claim an
audit validation that is not present.

## Triage

`theorem`; resolution `proved` for the exact joint A376317/A376388 conjecture
quoted above. The result settles both periodic shifts for every natural index.
Other A006318 identities, the source entries' main sequences, and claims of
global literature priority remain outside this dossier.

## ASSUMED-UNVERIFIED

The literature scope is bounded by the cited Library note. Global priority,
exhaustive absence of prior proofs, and the status of inaccessible or
unpublished work remain unverified. The typed escape audit is unresolved as
disclosed above; no `declared_validated` registration is claimed.
