---
slug: bala3634-type-one
bibkey: bala2023sqrtminusthree
doi: null
url: https://oeis.org/A363411
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/BalaA363411TypeOne.result
---

# Type-one primes through 101

## Problem

$\forall p\le101$, the primes dividing no $a(n)$ are exactly $\{3,11,17,23,29,41,47,53,59,83,89,101\}$, with the term index $n$ unbounded.
Here $a(n)$ and $b(n)$ are the integer coordinates of
$\prod_{k=0}^n(1+k\sqrt{-3})$.
Preregistration #18634 maps to `D5.S3.Arith.Congruence.BalaA363411TypeOne.result` (Proved).

## Motivation

This is an explicit OEIS conjecture in the source family documented in
[bala3634-valuations.md](bala3634-valuations.md).

## Gap

The source and literature screen recorded in #18634 found no proof of this
exact assertion in the searched scope; completeness is ASSUMED-UNVERIFIED.

## Route

`BalaA363411TypeOne.nonzero_of_block` extends each nonzero residue block to
all indices by strong induction. `BalaA363411.real_one` handles the prime $3$;
`listed_data` and `unlisted_data` certify the exact finite prime list. The primary
dossier gives the four issue-to-result mappings.

## Falsifier

An index or prime within the displayed domain violating the assertion would
refute it.

## Evidence

The kernel-checked declaration is
`D5.S3.Arith.Congruence.BalaA363411TypeOne.result`.
The axiom closure of every public declaration is contained in
{propext, Classical.choice, Quot.sound}.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| $\forall p\le101$, the primes dividing no $a(n)$ are exactly $\{3,11,17,23,29,41,47,53,59,83,89,101\}$, with the term index $n$ unbounded. | proved | Kernel-checked `BalaA363411TypeOne.result`. |

### What the settlement shows

The conclusion holds throughout its stated domain. The primary dossier gives
the shared mechanism and distinguishes the finite prime bound from the unbounded
term indices. Broader classifications remain open there.

## ASSUMED-UNVERIFIED

Literature completeness and priority are ASSUMED-UNVERIFIED. Four-slot escape
registration is unfinished in [#21978](https://github.com/the-omega-institute/trureturing/issues/21978);
no declared_validated status is asserted.
