---
slug: gurses-pekcan-2025-higher-hirota-four-soliton
bibkey: gurses2025higher
doi: 10.48550/arXiv.2511.18466
url: https://arxiv.org/abs/2511.18466v1
triage: theorem
motivation_gids:
  - D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.result
---

# Gürses and Pekcan's four-soliton conjecture for higher order Hirota forms

## Problem

Gürses and Pekcan study the Hirota bilinear equations

> D_x(D_x³+α₁D_t+α₂D_y)^{2k+1}{f·f}=0, k=0,1,2,…

For soliton parameters `p_i = (k_i, ω_i, l_i)` the operator has the polynomial
`P(p) = k(k³+α₁ω+α₂l)^{2k+1}`, and the dispersion relation is
`ω_i = −(k_i³+α₂l_i)/α₁`. The paper proves three-soliton solutions for every
`k` and `(α₁,α₂) ≠ (0,0)`, records the four-soliton condition for `k = 1`, and
states, after "we conjecture that the following lemma is valid for all k":

> The equation (bilinearProb2) has four-soliton solution only for k=0. For
> k≥1, it does not satisfy the four-soliton solution condition (4SC)
> directly.

Issue #10059 fixes the readings: the dispersion relation is
`k³ + α₁ω + α₂l = 0`, which also covers `α₁ = 0`; the four-soliton condition
is the eight-term display of the source's introduction with the last factor of
the fifth term read as `P(p₁+p₂+p₃−p₄)` (the source prints
`P(p₁−p₂+p₃−p₄)`, the last factor of the seventh term, and with that factor
the condition fails already for `k = 0`); "has four-soliton solution for
`k = 0`" is read as the condition vanishing at all parameters satisfying the
dispersion relation, and "does not satisfy (4SC) directly" as the existence,
for each `k ≥ 1`, of such parameters at which it does not vanish.

## Motivation

The frozen declaration
`D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.result` proves the
conjectured lemma for all real `(α₁,α₂) ≠ (0,0)`: the four-soliton condition
vanishes identically on the dispersion relation for `k = 0`, and for every
`k ≥ 1` it is negative at the wave numbers `(1, 3, 4, 5)`. The `k = 0`
equation is a Kadomtsev–Petviashvili-type model of shallow-water waves; the
result says that raising its dispersive operator to an odd power `2k + 1 ≥ 3`
keeps three-soliton solutions but destroys Hietarinta's four-soliton test.

## Gap

Issue #10059 preregisters this published conjecture and its literature
check. MathDB searches for "four-soliton", "Hirota bilinear" and "Gurses"
return no entry for it; Crossref records no citation of the journal version;
the authors' three later arXiv papers treat nonlocal reductions and exact
solutions of AKNS, NLS and MKdV systems; an arXiv abstract search for
four-soliton Hirota conditions returns only the source among recent papers.
The source checks `k = 1, 2, 3`.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

On the dispersion relation `α₁ω_i + α₂l_i = −k_i³`, and the map
`(k, ω, l) ↦ (k, α₁ω + α₂l)` is additive, so every value of `P` at a signed
sum of parameters equals `x(x³ + e)^m` with `x` the signed sum of the wave
numbers and `e` minus the signed sum of their cubes. For `m = 1` the
condition becomes a polynomial identity in `k₁, …, k₄`, which holds.

For `m = 2k + 1 ≥ 3` take `k = (1, 3, 4, 5)` with `ω_i = −k_i³/α₁, l_i = 0`
(or `ω_i = 0, l_i = −k_i³/α₂` when `α₁ = 0`). Each of the eight terms is a
product of seven factors `x(x³+e)^m`, and the condition equals
`48 · 1360488960000^m · F(m)` with

`F(m) = 13·11^m − 55·(−31)^m + 392·56^m + 525·21^m + 162·18^m − 350·14^m − 567·63^m − 120·(−24)^m`.

For odd `m` the positive terms total at most `1267·56^m`, and
`1267·56^m < 567·63^m` for `m = 7` and hence, multiplying by `56 < 63`, for
every `m ≥ 7`; `F(3) = −64774080` and `F(5) = −342030427200`. So `F(m) < 0`
for every odd `m ≥ 3`.

## Falsifier

A refutation of the `k = 0` part would be parameters on the dispersion
relation with a nonzero condition; the polynomial identity excludes them. A
refutation of the `k ≥ 1` part would need the condition to vanish at every
point of the dispersion relation for some `k ≥ 1`; the witness `(1, 3, 4, 5)`
gives a negative value for every such `k`.

## Evidence

Exact rational evaluation with the three-component polynomial `P`: the
corrected condition vanishes for `m = 1` at 30 random points of the dispersion
relation, including points with `α₁ = 0`; for `m = 3` it equals the source's
printed `k = 1` expression at `k = (1,3,4,5)`, `(2,−3,5,7)` and `(1,2,6,−9)`;
the condition as printed is `−380849837506560000` at `m = 1`,
`k = (1,3,4,5)`, `α = (1,0)`, while the corrected one is `0`; `F(m) < 0` for
every odd `m` with `3 ≤ m ≤ 401` (`F(1) = 0`). The Lean proof has only the standard axiom closure
`propext`, `Classical.choice`, and `Quot.sound`. These finite checks support
the reading but do not establish the universal theorem.

## Triage

First-tier external named open problem: Gürses and Pekcan, arXiv:2511.18466
(2025), the conjectured lemma after Remark 3 in the subsection on
`D_x(D_x³+α₁D_t+α₂D_y)^{2k+1}{f·f}=0`, preregistered in issue #10059.
Resolution: `proved`, for the four-soliton condition with the fifth term
corrected.

The public surface is exactly `hirotaP`, `dispersion`, `fourSC`, `claim`, and
`result`. This is a uniform theorem for every `k`, not bounded enumeration,
checker infrastructure, numeric reduction, or a certified finite instance, so
`utility: none` applies.

## ASSUMED-UNVERIFIED

The journal version, J. Phys.: Conf. Ser. 3264 (2026) 012016, was not read;
whether it keeps the conjecture and the printed fifth term is not known.
Semantic Scholar was rate-limited during the check. The bounded literature
check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent proof. The Lean kernel does not authenticate the
external source or its version history. The reading of "has four-soliton
solution" as Hietarinta's four-soliton condition follows the source's own use;
the existence of actual four-soliton solutions for `k = 0` is not formalized
here beyond that condition.
