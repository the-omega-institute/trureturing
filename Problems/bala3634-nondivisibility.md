---
slug: bala3634-nondivisibility
bibkey: bala2023sqrtminusthree
doi: null
url: https://oeis.org/A363412
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/BalaA363412.result
---

# Three-adic nondivisibility

## Problem

$3\nmid b(3n+1)$ for every $n\in\mathbb N$, including zero.
Here $a(n)$ and $b(n)$ are the integer coordinates of
$\prod_{k=0}^n(1+k\sqrt{-3})$.
Preregistration #18635 maps to `D5.S3.Arith.Congruence.BalaA363412.result` (Proved).

## Motivation

This is an explicit OEIS conjecture in the source family documented in
[bala3634-valuations.md](bala3634-valuations.md).

## Gap

The source and literature screen recorded in #18635 found no proof of this
exact assertion in the searched scope; completeness is ASSUMED-UNVERIFIED.

## Route

`BalaA363411.seq_period` gives period $3$ modulo $3$, and
`BalaA363411.seq_mod` reduces $3n+1$ to $1$. `seq_cast` identifies the
imaginary coordinate with $b(3n+1)$, whose residue is $1$. The primary
dossier gives the four issue-to-result mappings.

## Falsifier

An index or prime within the displayed domain violating the assertion would
refute it.

## Evidence

The kernel-checked declaration is
`D5.S3.Arith.Congruence.BalaA363412.result`.
The axiom closure of every public declaration is contained in
{propext, Classical.choice, Quot.sound}.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| $3\nmid b(3n+1)$ for every $n\in\mathbb N$, including zero. | proved | Kernel-checked `BalaA363412.result`. |

### What the settlement shows

The conclusion holds throughout its stated domain. The primary dossier gives
the shared mechanism and distinguishes the finite prime bound from the unbounded
term indices. Broader classifications remain open there.

## ASSUMED-UNVERIFIED

Literature completeness and priority are ASSUMED-UNVERIFIED. Four-slot escape
registration is unfinished in [#21978](https://github.com/the-omega-institute/trureturing/issues/21978);
no declared_validated status is asserted.
