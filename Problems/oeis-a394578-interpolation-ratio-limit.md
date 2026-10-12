---
slug: oeis-a394578-interpolation-ratio-limit
bibkey: kimberling2026a394578
doi: null
url: https://oeis.org/A394578/internal
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation
---

# The ratio-limit assertion for A394578

## Problem

The selected source COMMENT is:

> Conjecture: a(n+1)/a(n) -> 1/4.

Its complete native definition is quoted in the corresponding Library
note. For every natural n, p_n is the rational Lagrange polynomial
through (1,0) and (k,1) for all integers k from 2 through n+1. Define
$a_n=(4^n/2)p_n(n+1/2)$, including zero. The exact settling declaration
is `OEISA394578RatioRefutation.result : Not claim`, where `claim : Prop`
is convergence of the real consecutive ratio at natural `atTop` to 1/4.
The degree and node conditions have no extra hypothesis; no shifted
sequence or recurrence replaces the interpolation definition.

## Motivation

Moving the evaluation point with the interpolation order changes the
sequence's asymptotic behavior. A uniform interpolation error enclosure
already decides whether the printed ratio limit is compatible with the
native sequence.

## Gap

The source-specific Library note records the bounded literature and
supplier search. No exact prior settlement was found in that scope.
This is a tier-1 named OEIS conjecture. Issue
https://github.com/the-omega-institute/trureturing/issues/15665
contains the source-exact pre-probe registration. The settlement uses
`admission_basis: open-problem-resolution` and `proof_shape: bind-only`;
no escape witness or companion theorem is claimed.

## Route

The native interpolation sum is one minus the basis polynomial for
node 1, by Mathlib's sum-of-bases identity. At n+1/2 its error is

$$
\prod_{j=0}^{n-1}\frac{n-j-3/2}{-(j+1)}.
$$

Reversing the numerator product gives absolute factors $|j-1/2|$.
The first factor contributes 1/2 and all subsequent factors are bounded
by the corresponding positive denominator factors. Thus for n>=1,
$1/2\le p_n(n+1/2)\le3/2$. The positive normalizing factor implies
$a_n>0$, and comparing adjacent enclosures gives $a_{n+1}/a_n\ge4/3$.
A real limit of 1/4 contradicts this eventual bound by `ge_of_tendsto`.
All intermediate propositions are proof-local terms of the single result.

## Falsifier

Any exact prior settlement, a mismatch with the native source nodes or
normalization, an unproved positive tail denominator, or a nonstandard
axiom in the retained closure invalidates this candidate. Finitely many
initial terms alone cannot refute a ratio-limit assertion.

## Evidence

The canonical selected Lean target compiles the exact closed negation.
Its only mathematical source declarations are `p`, `a`, `claim` and
`result`. The Scribe result has one
`OpenProblemResolutionClaim(Refuted)` for this dossier. The utility
header identifies the literal claim and result selectors. The designated
refutation result is exempt from four-slot Reg registration under the
current contract; there are no other public theorem targets.

## Triage

The claimed limit is refuted by the uniform positive-tail bound. The
mechanism is the normalizing factor four between adjacent orders,
together with an interpolant constrained between one half and three
halves. The independent D-finiteness conjecture, exact limiting value,
recurrence and integrality remain outside this result. No statement
about their truth is made. The source's displayed interpolation
program remains the definition used here.

## ASSUMED-UNVERIFIED

Global completeness of the literature search is unverified; the checked
scope is listed in the Library note. Independent review, freezing and
integration are separate required steps. No assumption about a correct
limit or a conjectured recurrence enters the Lean proof.
