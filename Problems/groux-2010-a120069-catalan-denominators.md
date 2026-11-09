---
slug: groux-2010-a120069-catalan-denominators
bibkey: oeis2010a120069
doi: null
url: https://oeis.org/A120069
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/GrouxA120069Denominator.result
---

# Groux's original A120069 denominator conjecture

## Problem

OEIS A120069, FORMULA, Groux Roland, Dec 11 2010:

> Conjecture: a(n) = denominator(Catalan(n)/4^(n-1)). - Groux Roland, Dec 11 2010

With the ordinary Catalan numbers $C_k=\binom{2k}{k}/(k+1)$, the entry
has offset one and defines $a(n)$ as the positive reduced rational denominator
of $r_n=\sum_{k=1}^n C_k/4^{k-1}$. The complete assertion is
$\operatorname{den}(r_n)=\operatorname{den}(C_n/4^{n-1})$ for every
integer $n\ge1$. The sum includes both endpoints. All divisions are rational,
and the denominator is taken after reduction. The separate A283208 conjecture
in the same entry is outside this problem.

## Motivation

This is a first-tier explicit external OEIS conjecture with a source-native
finite-sum argument. Positive integer indices correspond exactly to natural
indices satisfying $0<n$. The intended result covers the complete original
range, without a finite cutoff or convergence assumption. Prospective source
qualification and the original event are in
[issue 27467](https://github.com/the-omega-institute/trureturing/issues/27467).

## Gap

Bounded qualification identified no complete prior denominator proof. Current
primary-source retrieval at 2026-11-07T00:31Z still finds the conjecture in
A120069 revision 30 (2026-03-10); A119951 revision 32 (2025-02-16) retains
Mostert's finite-sum identity. The identity is an established supplier, not a
separate newly resolved problem. No worldwide-priority claim follows from
these readings.

## Route

Use the Catalan form of Pieter Mostert's A119951 identity:
$r_n=4-(2n+1)q_n$, where $q_n=C_n/4^{n-1}$. The private finite-sum helper
is proved by induction from pinned Mathlib Catalan and central-binomial
relations. The reduced denominator of $q_n$ divides $4^{n-1}$, so it is
coprime to the odd integer $2n+1$. Mathlib's rational-denominator formulas
then give $\operatorname{den}((2n+1)q_n)=\operatorname{den}(q_n)$;
subtracting from the integer four preserves that denominator.

All three authored theorems have proof_shape: bind-only. The private
`balance` is consumed by `sum_formula`, and `sum_formula` by the sole public
`result`. Admission is open-problem-resolution; no escape witness or novel
supplier proof step is claimed. The mathematical proof imports only pinned
Mathlib, with no frozen project theorem prerequisite.

## Falsifier

A positive integer index whose two positive reduced denominators differ
would refute the original assertion. Agreement at finitely many indices,
including the initial index one, cannot prove the universal statement.

## Evidence

- Primary statement and definitions: https://oeis.org/A120069, NAME,
  COMMENTS, FORMULA and offset one; current revision history:
  https://oeis.org/history?seq=A120069.
- Attributed supplier: https://oeis.org/A119951, COMMENT, Pieter Mostert,
  Oct 12 2012; history: https://oeis.org/history?seq=A119951.
- Library source: `Library/ArithUnits/oeis2010a120069.md`.
- Exact result: `D5/S3/ArithSums/GrouxA120069Denominator.result`, universally
  quantified over natural $n$ with $0<n$, using `Finset.Icc 1 n`, rational
  casts and `Rat.den`. Its proof uses the standard three axioms only.
- Complete derivation and source correspondence:
  `Blueprint/D5/S3/ArithSums/GrouxA120069Denominator.scribe.cs`.
- Typed audit mirror:
  `Reg/D5/S3/ArithSums/GrouxA120069Denominator.lean`; its `.unknown`
  continuation leaves only the residual open and asserts no undecidability.

The original bounded qualification covered the linked Lang text, related
Mattarei weighted-sum work, selected original-wording and semantic queries,
MSE/MO identifier queries, project all-state issues/PRs and published
problems, and public MathDB identifier/semantic queries. No complete target
proof was identified in that inspected scope. The current refresh of project
all-state A120069/A119951 searches finds the owning preregistration and an
unrelated preregistration mentioning it; MathDB exact-ID queries return only
unrelated fuzzy records. Capped lists are not exhaustive. Current repository
search finds this result and its own mirrors, without a corresponding theory
volume or another complete target.

## Triage

`theorem`: the full original positive-index equality, with ordinary Catalan
numbers and positive reduced rational denominators. The source's mention of
a convergent series supplies no additional hypothesis to this finite result.

## ASSUMED-UNVERIFIED

The source-to-Lean identification and literature completeness are external
to the Lean kernel. The source/status search is bounded and establishes no
exhaustive absence, first-publication priority or originality of proof steps.
Unrelated MathDB hits do not supply a target solution count. Formal truth,
independent source-fidelity review, required CI and merged publication remain
distinct forms of evidence.
