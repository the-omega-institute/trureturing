---
slug: bala3634-paired-valuations
bibkey: bala2023sqrtminusthree
doi: null
url: https://oeis.org/A363412
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/BalaA363412Valuation.result
---

# Paired three-adic valuations

## Problem

$v_3(b(3n))=v_3(b(3n-1))$ for every $n\in\mathbb N$ with $n\ge1$.
Here $a(n)$ and $b(n)$ are the integer coordinates of
$\prod_{k=0}^n(1+k\sqrt{-3})$.
Preregistration #18636 maps to `D5.S3.Arith.Congruence.BalaA363412Valuation.result` (Proved).

## Motivation

This is an explicit OEIS conjecture in the source family documented in
[bala3634-valuations.md](bala3634-valuations.md).

## Gap

The source and literature screen recorded in #18636 found no proof of this
exact assertion in the searched scope; completeness is ASSUMED-UNVERIFIED.

## Route

`BalaA363412.reflection_congruences` states that $2b(m)-m(m+1)$ is
divisible by both $3m$ and $3(m+1)$. At $m=3n$ and $m=3n-1$,
`BalaA363412Valuation.at_multiple` and `before_multiple` convert these
divisibilities into factorizations of twice each imaginary coordinate as
$3n$ times an integer prime to $3$. Their helper
`BalaA363412Valuation.double_factor` applies `padicValInt.mul` to obtain
valuation $v_3(3n)$ on both sides. The primary dossier gives the four
issue-to-result mappings.

## Falsifier

An index or prime within the displayed domain violating the assertion would
refute it.

## Evidence

The kernel-checked declaration is
`D5.S3.Arith.Congruence.BalaA363412Valuation.result`.
The axiom closure of every public declaration is contained in
{propext, Classical.choice, Quot.sound}.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| $v_3(b(3n))=v_3(b(3n-1))$ for every $n\in\mathbb N$ with $n\ge1$. | proved | Kernel-checked `BalaA363412Valuation.result`. |

### What the settlement shows

The conclusion holds throughout its stated domain. The primary dossier gives
the shared mechanism and distinguishes the finite prime bound from the unbounded
term indices. Broader classifications remain open there.

## ASSUMED-UNVERIFIED

Literature completeness and priority are ASSUMED-UNVERIFIED. Four-slot escape
registration is unfinished in [#21978](https://github.com/the-omega-institute/trureturing/issues/21978);
no declared_validated status is asserted.
